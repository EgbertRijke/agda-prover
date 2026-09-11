{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.NNUE.Hash (sha256, featureHash) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Crypto.Hash.BLAKE2.BLAKE2b qualified as B
import Crypto.Hash.SHA256 qualified as SHA
import Data.Bits ((.|.), shiftL)
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Word (Word64)
import Foreign.C.Types (CInt (..))
import Foreign.ForeignPtr (mallocForeignPtr, withForeignPtr)
import Foreign.Ptr (Ptr, castPtr)
import Numeric (showHex)
import System.IO.Unsafe (unsafePerformIO)

sha256 :: BS.ByteString -> String
sha256 = concatMap byteHex . BS.unpack . SHA.hash
 where
  byteHex byte = let digits = showHex byte "" in replicate (2 - length digits) '0' ++ digits

-- The existing feature contract uses unkeyed BLAKE2b-64 with personalization,
-- not a prefix or a keyed hash. The upstream package exposes the reference C
-- initializer, but its Haskell convenience API exposes only ordinary/keyed
-- initialization. A fixed, validated parameter block supplies personalization.
-- State allocation/alignment and update/finalization stay with that package.
foreign import ccall unsafe "blake2b_init_param"
  initializeParameters :: Ptr () -> Ptr () -> IO CInt

featureHash :: Text -> Word64
featureHash input = unsafePerformIO $ do
  state <- mallocForeignPtr :: IO B.BLAKE2bState
  let parameters = BS.pack [8, 0, 1, 1] <> BS.replicate 44 0
                <> "AgdaProverP0" <> BS.replicate 4 0
  status <- withForeignPtr state $ \target ->
    BS.useAsCString parameters (initializeParameters (castPtr target) . castPtr)
  unless (status == 0) $ ioError $ userError "feature-hash-initialization-failed"
  let digest = B.finalize 8 (B.update (encodeUtf8 input) state)
  evaluate $ BS.foldr (\byte result -> fromIntegral byte .|. shiftL result 8) 0 digest
{-# NOINLINE featureHash #-}
