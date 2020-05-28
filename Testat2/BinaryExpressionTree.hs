{- |
Module      :  BinaryExpressionTree
Author      :  David Luthiger

Module containing the datatype and operation definitions for the binary expression tree datatype.
-}

module BinaryExpressionTree where

{-

The aim of this exercise is to test if you are able to:  
- Define algebraic datatypes  
- Define recursive functions on algebraic datatypes  
- Interpret types and kinds correctly    
- Define your own instances of type classes  

**Task 1**

Define the datatype `Tree n l` for non-empty binary trees with node items of type `n` and leaf items of type `l`. The type constructor `Tree` would therefore have the kind `* -> * -> *` and the following two data constructors:  
- `Leaf` of type `l -> Tree n l`  
- `Node` of type `n -> Tree n l -> Tree n l -> Tree n l`  

This datatype could, for instance be used to represent arithmetic expressions containing only binary operations, for instance:  
- `Node "PLUS" (Leaf 1) (Leaf 2) :: Tree [Char] Integer`  
- `Node "CONCAT" (Leaf "abc") (Leaf "def") :: Tree [Char] [Char]`  
- `Node (+) (Leaf 1) (Leaf 2) :: Tree (Integer -> Integer -> Integer) Integer`  
- `Node (++) (Leaf "abc") (Leaf "def") :: Tree ([a] -> [a] -> [a]) [Char]`  

-}

--  START Solution --
data Tree n l = Leaf l | Node n (Tree n l) (Tree n l)
--  END Solution --

{- 

The comments starting with `-- $>` are suggestions for ghci REPL queries that you can use to check the correctness of your solutions.

Optionally, you may also install and use the ghcid tool (https://github.com/ndmitchell/ghcid) with the `--allow-eval` option in order to execute such commands automatically after each file change using the following command:

ghcid -c stack ghci --allow-eval --clear --reverse-errors --no-height-limit BinaryExpressionTree.hs

Make sure that you run this command in an appropriately large terminal window.
Make sure that you separate each individual `-- $>` command with an additional newline. Otherwise, ghcid will regard this as one command split over multiple lines.
Note that you will get a number of errors when you run this command on this file before you add your solution to it since the REPL commands assume that the soluton is already present. A good way to avoid this could be to add an additional `-- ` at the start of each `-- $>` command until the solution is in place.

More information on installing and using ghcid can be found at the following links:
https://github.com/ndmitchell/ghcid 
https://www.parsonsmatt.org/2018/05/19/ghcid_for_the_win.html 
https://jkeuhlen.com/2019/10/19/Compile-Your-Comments-In-Ghcid.html 

-}

-- $> :k Tree

-- $> :t Leaf

-- $> :t Node

-- $> expr1 = Node "PLUS" (Leaf 1) (Leaf 2)

-- $> expr2 = Node "CONCAT" (Leaf "abc") (Leaf "def")

-- $> expr3 = Node (+) (Leaf 1) (Leaf 2)

-- $> expr4 = Node (++) (Leaf "abc") (Leaf "def")

-- $> :t expr1

-- $> :t expr2

-- $> :t expr3

-- $> :t expr4

{-

**Task 2.1**

Define the function `equals :: (Eq n, Eq l) => Tree n l -> Tree n l -> Bool` that compares two trees of the same type for equality.  

-}

--  START Solution --
equals :: (Eq n, Eq l) => Tree n l -> Tree n l -> Bool
equals (Leaf leaf1) (Leaf leaf2) = if leaf1 == leaf2 then True else False
equals (Node root1 leftTree1 rightTree1) (Node root2 leftTree2 rightTree2)
  = if root1 == root2 && equals leftTree1 leftTree2 && equals rightTree1 rightTree2 then True else False
equals _ _ = False
--  END Solution --

-- $> equals expr1 (Leaf 2)

{-

**Task 2.2**

Use the function `equals` that you have just defined to make the type `Tree` an instance of the typeclass `Eq`.  

-}

--  START Solution --
instance (Eq n, Eq l) => Eq (Tree n l) where x == y = equals x y
--  END Solution --

{-

**Task 3.1**

Define the function `showInorder` that returns the string representation of an inorder traversal of a tree. For instance:  
- `showInorder (Node "PLUS" (Leaf 1) (Leaf 2)) == "(1 \"PLUS\" 2)"`  
- `showInorder (Node "CONCAT" (Leaf "abc") (Leaf "def")) ==  "(\"abc\" \"CONCAT\" \"def\")"`  

Use the function `show :: Show a => a -> String` to get the string representation of a leaf or node item within your definition of `showInorder`.  

-}

--  START Solution --
showInorder :: (Show n, Show l) => Tree n l -> String
showInorder (Leaf leaf) = show leaf
showInorder (Node root leftTree rightTree) = show leftTree ++ show root ++ show rightTree
--  END Solution --

-- $> :t show

-- $> :t showInorder

-- $> showInorder (Node "PLUS" (Leaf 1) (Leaf 2))

-- $> showInorder (Node "CONCAT" (Leaf "abc") (Leaf "def"))

{-

**Task 3.2**

Use the function `showInorder` that you have just defined to make the type `Tree` an instance of the typeclass `Show`.

-}

--  START Solution --
instance (Show n, Show l) => Show (Tree n l) where show = showInorder
--  END Solution --

{-

**Task 4**

Define the function `eval` that evaluates the expression represented by a tree of type `Tree (t -> t -> t) t` into a value of type `t`. For instance:  
- `eval (Node (+) (Leaf 1) (Leaf 2)) == 3`  
- `eval (Node (++) (Leaf "abc") (Leaf "def")) ==  "abcdef"`  

-}

--  START Solution --
eval :: Tree (t -> t -> t) t -> t
eval (Leaf leaf) = leaf
eval (Node function leftTree rightTree) = function (eval leftTree) (eval rightTree)
--  END Solution --

-- $> :t eval

-- $> eval (Node (+) (Leaf 1) (Leaf 2))

-- $> eval (Node (++) (Leaf "abc") (Leaf "def"))

{-

**Task 5**

Define the function `member` that checks whether a given value occurs as an item (at either a node or a leaf) within a tree. For instance:  
- `member 'a' (Node '+' (Leaf 'a') (Leaf 'b')) == True`  
- `member '-' (Node '+' (Leaf 'a') (Leaf 'b')) == False`  

Use the function `(==) :: Eq a => a -> a -> Bool` to check for equality between leaf or node items within your definition of `member`.  

-}

--  START Solution --
member :: Eq a => a -> Tree a a -> Bool
member target (Leaf leaf) = if target == leaf then True else False
member target (Node root leftTree rightTree)
  = if root == target || member target leftTree || member target rightTree then True else False
--  END Solution --

-- $> :t member

-- $> member 'a' (Node '+' (Leaf 'a') (Leaf 'b'))

-- $> member '-' (Node '+' (Leaf 'a') (Leaf 'b'))
