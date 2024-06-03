module TestTersus where

import Parse

data Test = TestCase Bool | TestList [Test] deriving Show

testSafeHeadForEmptyList :: Test
testSafeHeadForEmptyList = 
    TestCase $ assertEqual "Should return Nothing for empty list"
                           Nothing (safeHead ([]::[Int]))

testSafeHeadForNonEmptyList :: Test
testSafeHeadForNonEmptyList =
    TestCase $ assertEqual "Should return (Just head) for non empty list" (Just 1)
               (safeHead ([1]::[Int]))

main :: IO Counts
main = runTestTT $ TestList [testSafeHeadForEmptyList, testSafeHeadForNonEmptyList]