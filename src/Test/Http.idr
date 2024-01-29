module Test.Http

import Control.Linear.LIO
import Control.Linear.Network
import Control.Linear.Network.RecvAll
import Data.Buffer
import Data.Fuel
import Data.List1
import Data.Nat
import Data.String
import Data.String.Extra1
import System

%hide Control.Linear.Network.recvAll

%default total

StatusCode : Type
StatusCode = Nat

namespace Header
  public export
  record Header where
    constructor MkHeader
    name : String
    value : String

  export
  Show Header where
    show (MkHeader name value) = "\{name}: \{value}"

  headerFromString : String -> Maybe Header
  headerFromString str =
    let
      a = Data.String.Extra1.split (== ':') str
    in case a of
      _ ::: Nil => Nothing
      name ::: (x :: xs) => Just $ MkHeader name (joinBy ":" $ ltrim x :: xs)

  export
  fromString : (str : String) -> {auto 0 prf : IsJust (headerFromString str)} -> Header
  fromString str {prf} with (headerFromString str)
    fromString str {prf = ItIsJust} | Just header = header

record Response where
  constructor MkResponse
  statusCode : StatusCode
  statusText : String
  headers : List Header
  body : Maybe String

Show Response where
  show (MkResponse code text headers body) =
    let
      statusLine = "HTTP/1.1 \{show code} \{text}"
      headerLines = show <$> headers
      lines = join
        [[statusLine]
        , headerLines
        , [""]
        , toList body
        ]
    in joinBy "\r\n" lines

HandleNext : Maybe SocketError -> Type
HandleNext Nothing = Socket Open
HandleNext (Just _) = Socket Closed

handle :
  LinearIO io =>
  (1 _ : Socket Open) ->
  L1 io (Res (Maybe SocketError) HandleNext)
handle soc = do
  Right requestStr # soc <- recvAll soc
  | Left err # soc =>
    pure1 $ Just err # soc

  putStrLn requestStr

  let
    body = "丐丐丐丑丑丑丠丠丠両両両"
    headers =
      [ MkHeader "Content-Type" "text/plain"
      , MkHeader "Content-Length" $ show $ stringByteLength body
      ]
    response = MkResponse 200 "OK" headers $ Just body

  Nothing # soc <- send soc $ show response
  | Just err # soc =>
    pure1 $ Just err # soc

  pure1 $ Nothing # soc

LoopNext : Maybe SocketError -> Type
LoopNext Nothing = Socket Listening
LoopNext (Just _) = Socket Closed

loop :
  LinearIO io =>
  Fuel ->
  (1 _ : Socket Listening) ->
  L1 io (Res (Maybe SocketError) LoopNext)
loop Dry soc = pure1 $ Nothing # soc
loop (More fuel) soc = do
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
  rec soc

  where
    rec : (1 _ : Socket Listening) -> L1 io (Res (Maybe SocketError) LoopNext)
    rec soc = loop fuel soc

succeed : LinearIO io => Fuel -> (1 _ : Socket Ready) -> L io ()
succeed fuel soc = do
  let port : Int := 5001

  -- Bind
  Nothing # soc <- bind soc (Just $ IPv4Addr 127 0 0 1) port
  | Just err # soc => do
    putStrLn "Error binding socket (errno: \{show err})"
    done soc

  -- Listen
  Nothing # soc <- listen soc
  | Just err # soc => do
    putStrLn "Error listening on socket (errno: \{show err})"
    done soc
  putStrLn "Listening on port \{show port}"

  Nothing # soc <- loop fuel soc
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
main = run $ newSocket AF_INET Stream 0 (succeed forever) fail
