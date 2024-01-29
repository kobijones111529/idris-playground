module Control.Linear.Network.RecvAll

import Control.Linear.LIO
import Control.Linear.Network

%default total

export
recvAll : LinearIO io => (1 _ : Socket Open) -> L1 io (Res (Either SocketError String) (\res => Next Receive (isRight res)))
recvAll soc = rec "" soc
  where
    rec : String -> (1 _ : Socket Open) -> L1 io (Res (Either SocketError String) (\res => Next Receive (isRight res)))
    rec acc soc = do
      let size = 65536

      Right (str, bytesRead) # soc' <- recv soc size
      | Left err # soc =>
        pure1 $ Left err # soc

      if bytesRead < size
        then pure1 $ Right (acc ++ str) # soc'
        else rec (acc ++ str) $ assert_smaller soc soc'
