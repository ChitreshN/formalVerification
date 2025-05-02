{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}

module Stack where

import Clash.Prelude

type Stacklength = 4

data StackState a n = StackState
  { stack :: Vec n a
  , stackIdx :: Index n
  }
  deriving (Generic, NFDataX)

stack ::
  forall n a.
  (KnownNat n, NFDataX a) =>
  StackState a n ->
  ( Maybe a -- push
  , Bool -- pop
  ) ->
  ( StackState a n
  , (Maybe a, Bool)
  )
stack state (dataIn, pop) = (updatedState, (poppedData, ready))
 where
  idx = state.stackIdx
  stack = state.stack
  valid = idx /= maxBound
  poppedData = if pop then Just (stack !! idx) else Nothing
  idx' = if pop then idx - 1 else idx

  (updatedStack, newIdx) = case (dataIn, valid) of
    (Just x, True) -> (replace (idx' + 1) x stack, idx' + 1)
    _ -> (stack, idx')

  updatedState = state{stack = updatedStack, stackIdx = newIdx}

  ready = newIdx /= maxBound

mkStack ::
  forall a dom.
  (HiddenClockResetEnable dom, NFDataX a, Default a) =>
  Signal dom (Maybe a, Bool) ->
  Signal dom (Maybe a, Bool)
mkStack = mealy stack initState
 where
  initState = StackState{stack = replicate (SNat @Stacklength) def, stackIdx = 0}
