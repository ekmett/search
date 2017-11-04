#!/usr/bin/runhaskell
\begin{code}
{-# OPTIONS_GHC -Wall #-}
import Distribution.Extra.Doctest ( defaultMainWithDoctests )
main :: IO ()
main = defaultMainWithDoctests "doctests"
\end{code}
