module Test.Http

import Control.Linear.LIO
import Control.Linear.Network

%default total

handle :
  LinearIO io =>
  (1 _ : Socket Open) ->
  L1 io (Res (Maybe SocketError) (\res => case res of { Nothing => Socket Open ; Just _ => Socket Closed }))
handle soc = do
  Right requestStr # soc <- recvAll soc
  | Left err # soc =>
    pure1 $ Just err # soc

  putStrLn requestStr

  Nothing # soc <- send soc "200"
  | Just err # soc =>
    pure1 $ Just err # soc

  pure1 $ Nothing # soc

covering
loop :
  LinearIO io =>
  (1 _ : Socket Listening) ->
  L1 io
    (Res
      (Maybe SocketError)
      (\res => case res of
        Nothing => Socket Listening
        Just _ => Socket Closed
      )
    )
loop soc = do
  Nothing # (soc # soc') <- accept soc
  | Just err # soc => do
    pure1 $ Just err # soc

  putStrLn "Accepted new connection"
  Nothing # soc' <- handle soc'
  | Just err # soc' => do
    putStrLn "Error handling request (errno: \{show err})"
    () <- done soc'
    pure1 $ Just err # !(close soc)

  soc' <- close soc'
  () <- done soc'

  loop' soc
  where
    loop' :
      LinearIO io' =>
      (1 _ : Socket Listening) ->
      L1 io'
        (Res
          (Maybe SocketError)
          (\res => case res of
            Nothing => Socket Listening
            Just _ => Socket Closed
          )
        )
    loop' soc = loop soc

covering
succeed : LinearIO io => (1 _ : Socket Ready) -> L io ()
succeed soc = do
  let port : Int := 5001

  -- Bind
  Nothing # soc <- bind soc Nothing port
  | Just err # soc => do
    putStrLn "Error binding socket (errno: \{show err})"
    done soc

  -- Listen
  Nothing # soc <- listen soc
  | Just err # soc => do
    putStrLn "Error listening on socket (errno: \{show err})"
    done soc
  putStrLn "Listening on port \{show port}"

  Nothing # soc <- loop soc
  | Just err # soc => do
    done soc

  -- Cleanup
  soc <- close soc
  done soc

fail : LinearIO io => Int -> L io ()
fail err = do
  putStrLn "Failed with code \{show err}"

export
covering
main : IO ()
main = run $ newSocket AF_INET Stream 0 succeed fail
