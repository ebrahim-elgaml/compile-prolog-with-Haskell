
data Variable  = A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|MyVariable|Fall deriving (Show,Eq)
data Constant a = Const a  deriving (Show,Eq)
data Term a = Constant (Constant a) | Variable Variable  deriving (Eq, Show)
data Predicate a = Pred String [Term a] deriving (Eq,Show)
data Goals a = Nil | Goal [Predicate a] deriving (Eq,Show)
data Rule a = Rulee (Predicate a) (Goals a) deriving (Eq,Show)
data Answer = Yes|No deriving (Show,Eq)
data Solution a = Sol Answer [(Variable,Term a)] deriving (Eq,Show)

equate [] [] = []
equate ((Variable b):xs) ((Constant a): ys) = (b ,(Constant a)): (equate xs ys)
equate ((Variable b):xs) ((Variable a): ys) = (b ,(Variable a)): (equate xs ys)
equate ((Constant b):xs) ((Variable a): ys) = equate (xs) ( ys)
equate ((Constant x):xs) ((Constant y):ys) |(Constant x)== (Constant y)  = (equate xs ys)
				           |otherwise                    = [(Fall , Constant x)]
   
equate ((Constant x):xs) [] = [(Fall , Constant x)]
equate []  ((Constant x):xs) = [(Fall , Constant x)]
equate ((Variable x):xs) [] = [(Fall , Variable x)]
equate []  ((Variable x):xs) = [(Fall , Variable x)]

checkLast [] = True
checkLast [(Fall ,Constant x)]= False
checkLast [(Fall ,Variable x)]= False
checkLast (x:xs) = checkLast xs
 
unifyWithHead (Pred x (xs:xs1)) (Pred y (ys:ys1)) | ((x==y) && checkLast(equate (xs:xs1) (ys:ys1))) = (Sol Yes (equate (xs:xs1) (ys:ys1)))
			       	                     | otherwise                            = (Sol No [])

equateItem (x,Constant (Const y))  [] = []
equateItem (x,Constant (Const y)) ((Constant b): ms) = (Constant b):equateItem (x,Constant (Const y)) ms
equateItem (x,Constant (Const y)) ((Variable b): ms)| (x==b)      =(Constant (Const y)):(equateItem (x,Constant (Const y))   ms)
	                                            | otherwise   =(Variable b):(equateItem (x,Constant (Const y))   ms)

equateItem (x,Variable y)  [] = []
equateItem (x,Variable y) ((Constant b): ms) = (Constant b):equateItem (x,Variable y) ms
equateItem (x,Variable y) ((Variable b): ms)| (x==b)      =(Variable y):(equateItem (x,Variable y)   ms)
	                                            | otherwise   =(Variable b):(equateItem (x,Variable y)   ms)

equatePred (Sol Yes ((x,Constant (Const y)):xs)) [] = []
equatePred (Sol Yes []) (m: ms) = (m:ms)
equatePred (Sol Yes []) [] = []
equatePred (Sol Yes ((x,Constant (Const y)):xs)) ((Constant b): ms) = ((Constant b): (equatePred (Sol Yes ((x,Constant (Const y)):xs))  ms))
equatePred (Sol Yes ((x,Constant (Const y)):xs)) ((Variable b): ms) = equatePred (Sol Yes xs) ((equateItem (x,Constant (Const y)) ((Variable b): ms)))

equatePred (Sol Yes ((x,Variable y):xs)) [] = []
equatePred (Sol Yes ((x,Variable y):xs)) ((Constant b): ms) = ((Constant b): (equatePred (Sol Yes ((x,Variable y):xs))  ms))
equatePred (Sol Yes ((x,Variable y):xs)) ((Variable b): ms) = equatePred (Sol Yes xs) ((equateItem (x,Variable y) ((Variable b): ms)))

applySolSubInBody (Sol Yes []) (Goal []) = (Goal [])
applySolSubInBody (Sol Yes []) (Goal (x:xs)) = (Goal (x:xs))
applySolSubInBody (Sol Yes [(x,Variable y)]) (Goal []) = (Goal [])
applySolSubInBody (Sol Yes ((x,Variable y):xs)) (Goal []) = (Goal [])
applySolSubInBody (Sol Yes ((x,Variable y):xs)) (Goal ((Pred p ps):ps1)) = Goal ((Pred p (equatePred (Sol Yes ((x , Variable y):xs)) ps)):g)                                                                               where Goal g = (applySolSubInBody (Sol Yes ((x,Variable y):xs)) (Goal ps1))
--applySolSubInBody (Sol Yes [_]) (Goal []) = (Goal [])
applySolSubInBody (Sol Yes [(x,Constant (Const y))]) (Goal []) = (Goal [])
applySolSubInBody (Sol Yes ((x,Constant (Const y)):xs)) (Goal []) = (Goal [])
applySolSubInBody (Sol Yes ((x,Constant (Const y)):xs)) (Goal ((Pred p ps):ps1)) = Goal ((Pred p (equatePred (Sol Yes ((x , Constant (Const y)):xs)) ps)):g)
                                                                                 where Goal g = (applySolSubInBody (Sol Yes ((x,Constant (Const y)):xs)) (Goal ps1))

--allSolutions (Pred p ps) ((Rulee (Pred p1 ps1) Nil ):r2) |(unifyWithHead (Pred p ps) (Pred p1 ps1) == (Sol Yes _ ))  = ((unifyWithHead (Pred p ps) (Pred p1 ps1)):(allSolutions (Pred p ps) r2))
                                                        -- | otherwise                                                 =  allSolutions (Pred p ps) r2
ifVariable (Variable a) = True
ifVariable (Constant a) = False

countVariable [] = 0
countVariable (x:xs) = if(ifVariable x) then 1+countVariable xs
					else countVariable xs

unifyWithHeadRule (x) (Rulee y b) = if (unifyWithHead x y /= (Sol No []))  
				    then applySolSubInBody (unifyWithHead x y) (b)
				    else Nil

found (x,y) [] = False
found (x,y) ((m,n):ms) = if (x==m && y==n) -- one item of the solution list and a body of solution list and search in it  
                         then True 
		              else found(x,y) ms
					  
foundVariable (x,y) [] = False
foundVariable (x,y) ((m,n):ms) = if (x==m ) -- one item of the solution list and a body of solution list and search in it  
                         then True 
		                   else foundVariable(x,y) ms
					  
soluAnd [] [] =[]
soluAnd a [] = a
soluAnd [] a = a   

soluAnd ((x,y):xs) ((m,n):ms) 
								|(not(foundVariable (x,y) ((m,n):ms)) && not(found (x,y) ((m,n):ms))) =soluAnd xs ((m,n):ms)--00
								|(not(foundVariable (x,y) ((m,n):ms)) && (found (x,y) ((m,n):ms))) =soluAnd xs ((m,n):ms)--01 impossible case
								|((foundVariable (x,y) ((m,n):ms)) && not(found (x,y) ((m,n):ms)))=[]--10
								|((foundVariable (x,y) ((m,n):ms)) && (found (x,y) ((m,n):ms))) = soluAnd xs ((m,n):ms)--11

soluAndReal x [] = False
soluAndReal x (y:ys) = if(soluAnd x y /=[]) -- takes a soltion and a list of solutions and anden the solution with the list
		       then True
		       else soluAndReal x ys

soluAndReal2  x [] = x
soluAndReal2  [] [] = []
soluAndReal2  [] y = []
soluAndReal2 (x:xs) (y:ys) = if( soluAndReal x (y:ys)) 
								then x:soluAndReal2 (xs) (y:ys)
								else soluAndReal2 (xs) (y:ys)

isFact (Rulee y b) = if (b==Nil) then True 
		                 else False

soluFact x ([]) y = []
soluFact (Pred a b) ((Rulee x y):xs) ((Rulee m n):ms) |( isFact (Rulee x y))  = unifyWithHead (Pred a b) x: soluFact (Pred a b) (xs) ((Rulee m n):ms)								
														| otherwise = soluFact (Pred a b) (xs) ((Rulee m n):ms)

flat [] = []
flat (x:xs) = x++flat xs	

getGoalBody (Goal a) = a
getGoalBody  Nil = []
						
solu1 [] ([]) x = []
solu1 y [] x = []
solu1 [] y x = []
solu1  ((Rulee x y):xs) ((Rulee m n):ms) (Pred a b) = if( isFact (Rulee x y))  
										 then unifyWithHead (Pred a b) x: solu1  (xs) ((Rulee m n):ms) (Pred a b)
										  else flat (map (solu1 ((Rulee m n):ms) ((Rulee m n):ms) ) (prdicatesList)) ++ solu1  (xs) ((Rulee m n):ms) (Pred a b)				  
										  where   (prdicatesList) =getGoalBody(unifyWithHeadRule (Pred a b) (Rulee x y)) 

getSolutionBody (Sol x y) | x == Yes = y
			  | otherwise =[]

getSolutionBta37btSolutions [] = []
getSolutionBta37btSolutions ((Sol x y):xs)| x == Yes = y:getSolutionBta37btSolutions xs
										| x==No =getSolutionBta37btSolutions xs
										
filterLength y [] = False
filterLength y x  = if(length x == y) 
					then True 
					else False
negateFilterLength y [] = False
negateFilterLength y x = if (filterLength y x ) then False
						else True
						
tryAllSolutions (Pred a b) (x) = soluAndReal2 n o 
		       where (m,n,o) =  (getSolutionBta37btSolutions(solu1  (x) (x) (Pred a b)),
                                        (filter (filterLength(countVariable b) )(m)),
                                        (filter (negateFilterLength(countVariable b) )(m)))

formSolution (x) = Sol Yes x

formAllSolutions [] = []
formAllSolutions (x:xs) = ((formSolution x) : formAllSolutions xs)


allSolutionsHelper x y = formAllSolutions (tryAllSolutions x y )

getVariableBody (Variable x) = x

swapVariables [] [] = []
swapVariables x [] = []
swapVariables [] y = []
swapVariables (x:xs) ((y,m):ys) = if(ifVariable x )
								then (getVariableBody x,m):swapVariables xs ys 
								else swapVariables xs ys
sh2lbConstantM3Variable (Constant (Const a)) = Variable MyVariable

yarb25rCaseNotHandled (Pred a ((Constant x):xs)) = Pred a ((sh2lbConstantM3Variable (Constant x)):xs) 

allSolutionHelper2MnGher25rCase (Pred a b) y = formAllSolutions( map (swapVariables b) (getSolutionBta37btSolutions(allSolutionsHelper (Pred a b) y)))								

foundTrue [] = False
foundTrue (x:xs) = if(x==True) 
					then True 
					else foundTrue xs

getFirstPredicateConstant (Pred a (x:xs)) = x

													
filterVariableConstantSolution [] = [] 
filterVariableConstantSolution ((x,Constant y):xs) = 
											(x,Constant y):(filterVariableConstantSolution xs)
filterVariableConstantSolution (x:xs) =filterVariableConstantSolution xs											 

getSolutionsHeadRule  x [] = []
getSolutionsHeadRule (Pred a b) ((Rulee x y):xs) = if( not(isFact (Rulee x y)))
												then unifyWithHead (Pred a b) x: getSolutionsHeadRule(Pred a b) xs
												else getSolutionsHeadRule (Pred a b) xs

allSolutionHelper2_B_25rCase a b | (allSolutionHelper2MnGher25rCase (yarb25rCaseNotHandled a) (b) /= [] &&
										 foundTrue(map (found (MyVariable ,getFirstPredicateConstant a)) (getSolutionBta37btSolutions (allSolutionHelper2MnGher25rCase (yarb25rCaseNotHandled a) (b))))) = [Sol Yes []]
										|otherwise =[]

appendSolutions [] [] = []
appendSolutions x [] = x
appendSolutions [] y = y
appendSolutions ((Sol Yes x):xs) y = ((Sol Yes x):xs) ++y

formHeadSolutions x y = formAllSolutions(map filterVariableConstantSolution (getSolutionBta37btSolutions(getSolutionsHeadRule x y)))
 
allSolutionsReal (Pred a b) y = if (countVariable b == 0) 
					then allSolutionHelper2_B_25rCase (Pred a b) y 
					else allSolutionHelper2MnGher25rCase (Pred a b) y 

allSolutions x y = appendSolutions (formHeadSolutions x y )(allSolutionsReal x y)
 
--allSolutions (Pred a b) y =  formAllSolutions( map (swapVariables b) (getSolutionL7btSolutions(allSolutionsHelper (Pred a b) y)))
--allSolutions x y = formAllSolutions (tryAllSolutions x y )
-- soluAnd ((x,y):xs) ((m,n):ms) = if(found (x,y) ((m,n):ms)) -- body of on solution and the body of the other solution
									-- then soluAnd xs ((m,n):ms)
									-- else []
-- solu1 x y z | otherwise  =[] 
-- solu x ([]) [] = []
-- solu x ([]) y = []
-- solu (Pred a b) ((Rulee x y):xs) ((Rulee m n):ms) = if( isFact (Rulee x y)) then 
										  -- unifyWithHead (Pred a b) x: solu (Pred a b) (xs) ((Rulee m n):ms)
										  -- else 
										  -- soluLPredicatesKteer (prdicatesList) ((Rulee m n):ms) ((Rulee m n):ms) ++ solu (Pred a b) (xs) ((Rulee m n):ms)
										  -- where  Goal (prdicatesList) =unifyWithHeadRule (Pred a b) (Rulee x y) 
											--solu x y m | otherwise = []

-- tryAllSolutions (Pred a b) (x) = soluAndReal2 n o 
		       -- where (m,n,o) =  (map (getSolutionBody) (solu (Pred a b) (x) (x)),
                                        -- (filter (filterLength(countVariable b) )(m)),
                                        -- (filter (negateFilterLength(countVariable b) )(m)))

 -- soluLPredicatesKteer [] [] [] = []
 -- soluLPredicatesKteer [] [] p = []
 -- soluLPredicatesKteer [] x [] = []
 -- soluLPredicatesKteer y [] [] = []
 -- soluLPredicatesKteer y x [] = []						 
 -- soluLPredicatesKteer y [] p = []
 -- soluLPredicatesKteer [] x p = []
 -- soluLPredicatesKteer (x:xs)(y:ys) p =  (solu (x)(y:ys) p ++ soluLPredicatesKteer xs (y:ys) p)

--allSolutions x y = (soluFact x y y )++formAllSolutions (tryAllSolutions x y )

--allSolutions (Pred "father" ([Variable A,Variable B])) (Rulee (Pred "male" [Constant (Const "Ahmed")]) [])

--allSolutions (Pred "father" ([Variable A,Variable B])) (Rulee (Pred "male" [Constant (Const "Ahmed")]) (Nil))
--allSolutions (Pred "father" ([Variable A,Variable B])) [(Rulee (Pred "male" [Constant (Const "Ahmed")]) Nil)]
--allSolutions (Pred "father" ([Variable A,Variable B])) [(Rulee (Pred "male" [Constant (Const(1))]) Nil),(Rulee (Pred "father" ([Constant (Cons 2),Constant (Cons3)])) (Nil))] 
--pattern match failure: applySolSubInBody (Sol Yes [(X,Variable X),(Y,Variable Y)]) (Goal [])
--applySolSubInBody (Sol Yes ((x,Variable y):xs)) (Goal []) = (Goal [])
--applySolSubInBody (Sol Yes [(X,Variable X),(Y,Variable Y)]) (Goal [])
-- solu1  [(Rulee (Pred "male" [(Constant (Const 1))]) Nil), 
-- (Rulee (Pred "parent" [(Constant (Const 1)), (Constant (Const 2))]) Nil),
-- (Rulee (Pred "maggie" [(Constant (Const 5)),(Constant (Const 2))]) Nil),
-- (Rulee (Pred "father" [(Variable A),(Variable B)]) (Goal [(Pred "male" [(Variable A)] ),(Pred "parent" [(Variable A),(Variable B)])]))] [(Rulee (Pred "male" [(Constant (Const 1))]) Nil), 
-- (Rulee (Pred "parent" [(Constant (Const 1)), (Constant (Const 2))]) Nil),
-- (Rulee (Pred "maggie" [(Constant (Const 5)),(Constant (Const 2))]) Nil),
-- (Rulee (Pred "father" [(Variable A),(Variable B)]) (Goal [(Pred "male" [(Variable A)] ),(Pred "parent" [(Variable A),(Variable B)])]))] (Pred "father" [Variable X,Constant(Const 4)])
-- [Sol No [],Sol No [],Sol No [],Sol Yes [(A,Constant (Const 1))],Sol No [],Sol No []
-- solu1  [(Rulee (Pred "male" [(Constant (Const 1))]) Nil), 
-- (Rulee (Pred "parent" [(Constant (Const "1")), (Constant (Const "2"))]) Nil),
-- (Rulee (Pred "maggie" [(Constant (Const "5")),(Constant (Const "2"))]) Nil),
-- (Rulee (Pred "father" [(Variable A),(Variable B)]) (Goal [(Pred "male" [(Variable A)] ),(Pred "parent" [(Variable A),(Variable B)])]))] [(Rulee (Pred "male" [(Constant (Const "1"))]) Nil), 
-- (Rulee (Pred "parent" [(Constant (Const "1")), (Constant (Const "2"))]) Nil),
-- (Rulee (Pred "maggie" [(Constant (Const "5")),(Constant (Const "2"))]) Nil),
-- (Rulee (Pred "father" [(Variable A),(Variable B)]) (Goal [(Pred "male" [(Variable A)] ),(Pred "parent" [(Variable A),(Variable B)])]))] (Pred "father" [Variable X,Constant(Const "4")])
-- Program error: pattern match failure: solu1_v1660 Nil
--map (found (MyVariable ,Constant (Const "amira")) --[Sol Yes [(MyVariable,Constant (Const "slim"))],Sol Yes [(MyVariable,Constant (Const "azmy"))]]
--unifyWithHeadRule (Pred "f" [Variable A, Constant (Const "maha"), Variable B, Variable C, Variable D]) (Rulee (Pred "f" [(Constant (Const "slim")), Variable X, (Constant (Const "mina")), Variable Y, Variable Z]) (Goal [Pred "f2" [Variable Z, Constant (Const "maha")]]))