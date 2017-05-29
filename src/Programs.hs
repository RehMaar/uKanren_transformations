module Programs where
import MuKanren

appendo a b ab =
  fun "appendo" $
      conde [ [ a === nil, b === ab ]
            , [ callFresh (\h ->
                  callFresh (\t ->
                    a === pair h t &&&
                    callFresh (\ab' ->
                      pair h ab' === ab &&& (call (appendo t b ab') [t, b, ab']))
                 )
                )
              ]
            ]

reverso a b =
  fun "reverso" $
      conde [ [a === nil, b === nil]
            , [callFresh (\h ->
                callFresh (\t ->
                    a === pair h t &&&
                    callFresh (\a' ->
                      (call (reverso t a') [t, a'])
                       &&&
                       (let h' = list [h] in (call (appendo a' h' b) [a', h', b]))
                  )
                )
              )]
            ]

revAcco xs acc sx =
  fun "revAcco" $
    conde [ [ xs === nil, sx === acc]
          , [ callFresh (\h ->
                callFresh (\t ->
                  xs === pair h t &&&
--                  callFresh (\y ->
--                    y === pair h acc &&&
--                    call (revAcco t y sx) [t, y, sx]
--                  )
                  (let y = pair h acc in call (revAcco t y sx) [t, y, sx])
                )
              )
            ]
          ]

{-
rotatelN ; lN :
rotatetL; N ; R; tL 0 ; N ; R 0 
rotatetL; N ; R; tR 0 ; N ; L 0 
rotateL; L 0 ; rotateR; R 0 :
rotateL; L 0 ; rotateR; R 0 :
prunelN ; lN :
prunetL; 0; R; l0:
prunetL; sN ; R; tL 0 ; sN ; R 0 
pruneL; L 0 ; pruneR; R 0 
-}

