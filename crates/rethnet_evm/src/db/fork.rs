use hashbrown::HashMap;
use revm::{db::DatabaseRef, Account, AccountInfo, Bytecode};

use rethnet_eth::{Address, B256, U256};

use crate::db::{
    layered_db::{LayeredDatabase, RethnetLayer},
    remote::{RemoteDatabase, RemoteDatabaseError},
};

struct ForkDatabase {
    layered_db: LayeredDatabase<RethnetLayer>,
    remote_db: RemoteDatabase,
    account_info_cache: HashMap<Address, AccountInfo>,
    code_by_hash_cache: HashMap<B256, Bytecode>,
    storage_cache: HashMap<(Address, U256), U256>,
}

#[derive(thiserror::Error, Debug)]
pub enum ForkDatabaseError {
    #[error(transparent)]
    RemoteDatabase(#[from] RemoteDatabaseError),

    #[error(transparent)]
    LayeredDatabase(#[from] <LayeredDatabase<RethnetLayer> as revm::Database>::Error),

    /// Some other error from an underlying dependency
    #[error(transparent)]
    OtherError(#[from] std::io::Error),
}

impl ForkDatabase {
    pub fn _new(url: &str) -> Self {
        Self {
            layered_db: LayeredDatabase::<RethnetLayer>::default(),
            remote_db: RemoteDatabase::_new(url),
            account_info_cache: HashMap::new(),
            code_by_hash_cache: HashMap::new(),
            storage_cache: HashMap::new(),
        }
    }
}

impl revm::Database for ForkDatabase {
    type Error = ForkDatabaseError;

    fn basic(&mut self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        if let Some(cached) = self.account_info_cache.get(&address) {
            Ok(Some(cached.clone()))
        } else {
            let to_be_cached = self
                .layered_db
                .basic(address)
                .map_err(ForkDatabaseError::LayeredDatabase)?
                .or(self
                    .remote_db
                    .basic(address)
                    .map_err(ForkDatabaseError::RemoteDatabase)?)
                .unwrap();

            self.account_info_cache
                .insert(address, to_be_cached.clone());

            if to_be_cached.code.is_some() {
                self.code_by_hash_cache
                    .insert(to_be_cached.code_hash, to_be_cached.code.clone().unwrap());
            }

            Ok(Some(to_be_cached))
        }
    }

    fn code_by_hash(&mut self, code_hash: B256) -> Result<Bytecode, Self::Error> {
        if let Some(cached) = self.code_by_hash_cache.get(&code_hash) {
            Ok(cached.clone())
        } else {
            let to_be_cached = self
                .layered_db
                .code_by_hash(code_hash)
                .map_err(ForkDatabaseError::LayeredDatabase)?;

            // remote_db doesn't support code_by_hash, so there's no delegation to it here.

            self.code_by_hash_cache
                .insert(code_hash, to_be_cached.clone());

            Ok(to_be_cached)
        }
    }

    fn storage(&mut self, address: Address, index: U256) -> Result<U256, Self::Error> {
        if let Some(cached) = self.storage_cache.get(&(address, index)) {
            Ok(*cached)
        } else {
            let to_be_cached = self
                .layered_db
                .storage(address, index)
                .map_err(ForkDatabaseError::LayeredDatabase)?;

            let to_be_cached = if to_be_cached == U256::from(0) {
                self.remote_db
                    .storage(address, index)
                    .map_err(ForkDatabaseError::RemoteDatabase)?
            } else {
                to_be_cached
            };

            self.storage_cache.insert((address, index), to_be_cached);

            Ok(to_be_cached)
        }
    }
}

impl revm::DatabaseCommit for ForkDatabase {
    fn commit(&mut self, changes: HashMap<Address, Account>) {
        self.layered_db.commit(changes)
    }
}

impl crate::DatabaseDebug for ForkDatabase {
    type Error = ForkDatabaseError;

    fn account_storage_root(&mut self, address: &Address) -> Result<Option<B256>, Self::Error> {
        self.layered_db
            .account_storage_root(address)
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Inserts an account with the specified address.
    fn insert_account(
        &mut self,
        address: Address,
        account_info: AccountInfo,
    ) -> Result<(), Self::Error> {
        self.layered_db
            .insert_account(address, account_info)
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Modifies the account at the specified address using the provided function.
    fn modify_account(
        &mut self,
        address: Address,
        modifier: crate::debug::ModifierFn,
    ) -> Result<(), Self::Error> {
        self.layered_db
            .modify_account(address, modifier)
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Removes and returns the account at the specified address, if it exists.
    fn remove_account(&mut self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        crate::DatabaseDebug::remove_account(&mut self.layered_db, address)
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Sets the storage slot at the specified address and index to the provided value.
    fn set_account_storage_slot(
        &mut self,
        address: Address,
        index: U256,
        value: U256,
    ) -> Result<(), Self::Error> {
        self.layered_db
            .set_account_storage_slot(address, index, value)
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Reverts the state to match the specified state root.
    fn set_state_root(&mut self, state_root: &B256) -> Result<(), Self::Error> {
        self.layered_db
            .set_state_root(state_root)
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Retrieves the storage root of the database.
    fn state_root(&mut self) -> Result<B256, Self::Error> {
        self.layered_db
            .state_root()
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Creates a checkpoint that can be reverted to using [`revert`].
    fn checkpoint(&mut self) -> Result<(), Self::Error> {
        self.layered_db
            .checkpoint()
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Reverts to the previous checkpoint, created using [`checkpoint`].
    fn revert(&mut self) -> Result<(), Self::Error> {
        self.layered_db
            .revert()
            .map_err(ForkDatabaseError::LayeredDatabase)
    }

    /// Makes a snapshot of the database that's retained until [`remove_snapshot`] is called. Returns the snapshot's identifier.
    fn make_snapshot(&mut self) -> B256 {
        self.layered_db.make_snapshot()
    }

    /// Removes the snapshot corresponding to the specified id, if it exists. Returns whether a snapshot was removed.
    fn remove_snapshot(&mut self, state_root: &B256) -> bool {
        self.layered_db.remove_snapshot(state_root)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::str::FromStr;

    fn get_alchemy_url() -> Result<String, String> {
        Ok(std::env::var_os("ALCHEMY_URL")
            .expect("ALCHEMY_URL environment variable not defined")
            .into_string()
            .expect("couldn't convert OsString into a String"))
    }

    #[test]
    fn basic_success() {
        let dai_address = Address::from_str("0x6b175474e89094c44da98b954eedeac495271d0f")
            .expect("failed to parse address");
        let mut fork_db =
            ForkDatabase::_new(&get_alchemy_url().expect("failed to get alchemy url"));
        let account_info =
            revm::Database::basic(&mut fork_db, dai_address).expect("should have succeeded");

        assert!(account_info.is_some());
        let account_info = account_info.unwrap();
        assert_eq!(account_info.balance, U256::from(0));
        assert_eq!(account_info.nonce, 0);
        assert_eq!(
            account_info.code_hash,
            B256::from_str("0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
                .expect("failed to parse")
        );
    }
}
