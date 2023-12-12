module Game.Game

import Data.DPair
import Data.Fin
import Data.String
import Data.Vect
import Data.Vect.AtIndex

%default total

public export
data Item = LandingGearPart | WarpDrivePart | EnginePart | Rifle | Scope

export
Show Item where
  show LandingGearPart = "Landing Gear Part"
  show WarpDrivePart = "Warp Drive Part"
  show EnginePart = "Engine Part"
  show Rifle = "Rifle"
  show Scope = "Scope"

export
itemDescription : Item -> String
itemDescription item = case item of
  LandingGearPart => "A component of your ship’s landing gear; one of the three parts needed to repair your ship."
  WarpDrivePart => "A component of your ship’s warp drive; one of the three parts needed to repair your ship."
  EnginePart => "A component of your ship’s engine; one of the three parts needed to repair your ship."
  Rifle => "A standard-issue combat rifle. Powerful, but very hard to aim without a scope.\n(Equipped as long as it is in your inventory)"
  Scope => "A scope for your rifle.\n(Equipped as long as it and the rifle are in your inventory)"

export
itemFromInputString : String -> Maybe Item
itemFromInputString string =
  let
    string : String := case strM string of
      StrNil => ""
      StrCons x xs => toLower x `strCons` xs
  in case string of
    "landing" => Just LandingGearPart
    "warp" => Just WarpDrivePart
    "engine" => Just EnginePart
    "rifle" => Just Rifle
    "scope" => Just Scope
    _ => Nothing

export
itemFromID : Fin 5 -> Item
itemFromID id = case id of
  0 => LandingGearPart
  1 => WarpDrivePart
  2 => EnginePart
  3 => Rifle
  4 => Scope

export
itemID : Item -> Fin 5
itemID item = case item of
  LandingGearPart => 0
  WarpDrivePart => 1
  EnginePart => 2
  Rifle => 3
  Scope => 4

export
Inventory : Type
Inventory = Vect 5 Bool

export
Nil : Inventory
Nil = replicate 5 False

export
(::) : Item -> Inventory -> Inventory
(::) x xs = replaceAt (itemID x) True xs

namespace View
  public export
  data ViewInventory : Inventory -> Type where
    Nil : ViewInventory Nil
    (::) : (x : Item) -> (xs : Inventory) -> ViewInventory (x :: xs)

export
[ShowInventory] Show Inventory where
  show inventory =
    let
      (_ ** inventory) = mapMaybe (uncurry $ \id, hasItem => guard hasItem *> pure (itemFromID id)) . zip range $ inventory
    in showHelp inventory
  where
    showHelp : Vect n Item -> String
    showHelp [] = "No items"
    showHelp [x] = show x
    showHelp [x, y] = "\{show x} and \{show y}"
    showHelp [x, y, z] = "\{show x}, \{show y}, and \{show z}"
    showHelp (x :: xs) = "\{show x}, \{showHelp xs}"

export
record Monster where
  constructor MkMonster
  health : Nat
  name : String
  description : String
  deathMessage : String

attack : Monster -> Nat -> Monster
attack = flip $ \dmg => { health $= (`minus` dmg) }

data RoomShape = Rectangle | Cicle | Diamond | WideEllipse | TallEllipse

mutual
  record Connections where
    constructor MkConnections
    north : Maybe Room
    east : Maybe Room
    south : Maybe Room
    west : Maybe Room

  record Room where
    constructor MkRoom
    connections : Connections
    name : String
    description : String
    shape : RoomShape
    items : Inventory
    canDig : Bool
    canExplode : Bool
    monster : Maybe Monster

record Player where
  constructor MkPlayer
  health : Nat
  inventory : Inventory

data EndState = Won | Lost | Exploded

record GameState where
  constructor MkGameState
  player : Player
  room : Room
  endState : Maybe EndState

displayRoom : Room -> String
displayRoom room =
  let
    a : Vect _ _ := map (\i => Data.String.replicate 10 ' ') $ the (Vect _ _) $ allFins 10
  in ?displ

describeRoom : Room -> String
describeRoom room =
  let
    digMsg = guard room.canDig *>
      Just "There is something sticking out of the dirt. You could dig it out with the right tool."
    explodeMsg = guard room.canExplode *>
      Just "There is something wedged underneath a cracked rock, but the rock is too heavy to move."
  in """
    \{room.description}

    You see \{show @{ShowInventory} room.items} in the room.

    """ ++ fromMaybe "" (digMsg <+> map ("\n" ++) explodeMsg)

startMessage : String
startMessage = """
  You wake up on an alien planet among the ruins of your spaceship.
  You appear to be the only survivor. You need to repair the ship and escape
  with your life. To do this, you will need to find a landing gear component,
  a warp drive component, and an engine component, which were scattered somewhere
  on the planet when the ship crashed. You will then need to return to the ship and
  repair it (by using any of the components with the use command)
  You can open the in-game menu at any time with the menu command
  see a list of instructions or quit (progress is not saved).
  You have only 40 hours of oxygen remaining.
  Moving will use up 1 hour of your oxygen. If you should come to any harm, your
  suit's medkit will heal you, but the chemical reactions it uses need oxygen,
  which it will take from your tank.

  Good luck!


  """

export
run : IO ()
run =
  let
    player = MkPlayer { health = 40, inventory = Nil }
    spaceship = MkRoom
      { connections = MkConnections
        { north = Nothing, east = Nothing, south = Nothing, west = Nothing }
      , name = "Spaceship wreckage"
      , description = "The wreckage of your spaceship"
      , shape = Diamond
      , items = Nil
      , canDig = False
      , canExplode = False
      , monster = Nothing
      }
    game = MkGameState { player = player, room = spaceship, endState = Nothing }
  in do
  putStrLn $ "\n" ++ startMessage
  putStrLn $ displayRoom game.room
  putStrLn $ describeRoom game.room
