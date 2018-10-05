restart

--NB: this code gives correct results only for homogeneous ideals

loadPackage("Depth");

--functions for intersecting ideals
--return the list of all components of all intersections of two lists
intersectLists = (list1,list2) -> (
    list1 = removeRedundantComponents(list1);
    list2 = removeRedundantComponents(list2);
    intersectionList := flatten for i to #list1 - 1 list for j to #list2 - 1 list list1#i + list2#j;
    intersectionList = removeRedundantComponents(intersectionList);
    componentsList := componentsOfTheList(intersectionList);
    componentsList = removeRedundantComponents(componentsList);
    return componentsList;
    )

--remove ideals that appear twice or contain a variable or sum of two variables or sum of certain four variables
removeRedundantComponents = (list1) -> (
    if(list1 == {}) then return {};
    --remove ideals that appear twice
    removeList := {};
    for i to #list1-1 do for j from i+1 to #list1-1 do if(list1#i == list1#j) then removeList = append(removeList,j);    
    list1 = removeFromList(list1,removeList);
    --remove ideals that contain a variable or a sum of two variables or a sum of four variables
    R := ring list1#0;
    variablesList := flatten for i to numgens R - 1 list R_i;
    sums2List := flatten for i to numgens R - 1 list for j from i + 1 to numgens R - 1 list R_i + R_j;
    sums4List := flatten flatten flatten for i to numgens R - 1 list 
                         for j from i + 1 to numgens R - 1 list 
			 for k from j + 1 to numgens R - 1 list
			 for l from k + 1 to numgens R - 1 list R_i + R_j + R_k + R_l;
    linearFormsList := join(variablesList,sums2List,sums4List);
    removeList = {};
    for i to #list1 - 1 do for j to #linearFormsList - 1 do (
	if(linearFormsList#j % list1#i == 0) then removeList = append(removeList,i);
	);
    list1 = removeFromList(list1,removeList);
    return list1;
    )

--remove elements of removeList from list1
removeFromList = (list1,removeList) -> (
    removeList = sort(unique(removeList));
    keepList := for i to #list1-1 list i;
    keepList = toList(set keepList - set removeList);
    list1 = keepList / (i -> list1#i);
    return list1;
    )

--construct the list of components
componentsOfTheList = (list1) -> (
    componentsList := flatten for i to #list1 - 1 list minimalPrimes list1#i;
    return componentsList;
    )

--functions for making the likelihood ideal
-- make likelihood ideal from original coordinates    
makeLikelihoodIdeal=(myIdeal)->(
    completeIntersectionIdeal:=makeCompleteIntersectionIdeal(myIdeal);
    likelihoodIdeal:=makeLikelihoodIdealFromCompleteIntersection(completeIntersectionIdeal);
    return likelihoodIdeal;
    )

--choose a regular sequence from the generators of the ideal to construct a complete intersection
makeCompleteIntersectionIdeal=(myIdeal)->(
    	c:=codim myIdeal;
	gensMyIdeal:=flatten entries gens myIdeal;
	nGens:=#gensMyIdeal;
	subsetsGens:=subsets(nGens,c);
	for i to #subsetsGens-1 do (
	    mySubset:=subsetsGens#i;
	    newGens:=mySubset/(x->gensMyIdeal#x);
	    if(isRegularSequence(newGens)) then (
		return ideal(newGens);
	    );
        );
    print("Did not find a complete intersection.");
	return ideal(0);
    )

--function that constructs the likelihood ideal of an ideal
--NB: the original ideal should not include the summing to one condition
makeLikelihoodIdealFromCompleteIntersection=(originalI)->(        
    c:= (numgens originalI);
    R:=QQ[p_(0,0,0)..p_(1,1,1),l_1..l_c];
    originalI=sub(originalI,R);
    augmentedJacobian:=makeAugmentedJacobian(originalI);
    augmentedJacobian=sub(augmentedJacobian,R);
    
    --construct the left kernel vector and the likelhood ideal
    uSum:=sum entries (transpose augmentedJacobian)_0;
    kernelVector:=matrix{join({1,-uSum},for i from 1  to c list l_i)};
    likelihoodIdeal:=originalI+ideal(kernelVector*augmentedJacobian);
    
    return likelihoodIdeal;
    )

--construct the augmented Jacobian matrix
makeAugmentedJacobian=(originalI)->(
    R2:=QQ[p_(0,0,0)..p_(1,1,1)];
    originalI=sub(originalI,R2);
    -- first row consists of random positive integers
    -- firstRow:=matrix{for i to 7 list random(1,100)};
    firstRow:=matrix{{17,5,27,5,16,5,19,6}};
    -- construct the second to last row of the augmented Jacobian
    -- the second row will correspond to the row of variables
    secondRow:=matrix{for i to 7 list 1};
    J:=transpose jacobian originalI;
    J=secondRow||J;
    -- multiply each column by the corresponding variable
    D:=matrix for i to 7 list for j to 7 list if i==j then (vars R2)_(0,i) else 0;
    lastRows:=J*D;
    augmentedJacobian:=firstRow||lastRows;
    return augmentedJacobian;
    )


--actual code starts here
R=QQ[p_(0,0,0)..p_(1,1,1)];

--the Zariski closure of the model
I=ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),
    p_(0,0,1)*p_(1,0,0)-p_(0,0,0)*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),
    p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p_(1,0,0)*p_(1,1,1));
   
inequalities = {p_(0,1,0)*p_(1,0,0)+p_(0,1,1)*p_(1,0,0)+p_(0,1,0)*p_(1,0,1)+p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)-p_(0,0,1)*p_(1,1,0)-p_(0,0,0)*p_(1,1,1)-p_(0,0,1)*p_(1,1,1),
      -p_(0,0,1)*p_(0,1,0)+p_(0,0,0)*p_(0,1,1)+p_(0,0,0)*p_(1,0,0)-p_(0,0,1)*p_(1,0,1)-p_(0,1,0)*p_(1,1,0)-p_(1,0,1)*p_(1,1,0)+p_(0,1,1)*p_(1,1,1)+p_(1,0,0)*p_(1,1,1),
      p_(0,0,0)*p_(0,1,0)-p_(0,0,1)*p_(0,1,1)-p_(0,0,1)*p_(1,0,0)+p_(0,0,0)*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)-p_(1,0,0)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1)+p_(1,0,1)*p_(1,1,1),
      p_(0,0,0)*p_(0,0,1)-p_(0,1,0)*p_(0,1,1)-p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(1,0,0)*p_(1,0,1)+p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1)+p_(1,1,0)*p_(1,1,1)};


originalIdeals={ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),
	p_(0,0,1)*p_(1,0,0)-p_(0,0,0)*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),
	p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p_(1,0,0)*p_(1,1,1),
	p_(0,1,0)*p_(1,0,0)+p_(0,1,1)*p_(1,0,0)+p_(0,1,0)*p_(1,0,1)+p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)-p_(0,0,1)*p_(1,1,0)-p_(0,0,0)*p_(1,1,1)-p_(0,0,1)*p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),
	  p_(0,0,1)*p_(1,0,0)-p_(0,0,0)*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),
	  p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p_(1,0,0)*p_(1,1,1),
	  -p_(0,0,1)*p_(0,1,0)+p_(0,0,0)*p_(0,1,1)+p_(0,0,0)*p_(1,0,0)-p_(0,0,1)*p_(1,0,1)-p_(0,1,0)*p_(1,1,0)-p_(1,0,1)*p_(1,1,0)+p_(0,1,1)*p_(1,1,1)+p_(1,0,0)*p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),
	  p_(0,0,1)*p_(1,0,0)-p_(0,0,0)*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),
	  p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p_(1,0,0)*p_(1,1,1),
	  p_(0,0,0)*p_(0,1,0)-p_(0,0,1)*p_(0,1,1)-p_(0,0,1)*p_(1,0,0)+p_(0,0,0)*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)-p_(1,0,0)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1)+p_(1,0,1)*p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),
	  p_(0,0,1)*p_(1,0,0)-p_(0,0,0)*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),
	  p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p_(1,0,0)*p_(1,1,1),
	  p_(0,0,0)*p_(0,0,1)-p_(0,1,0)*p_(0,1,1)-p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(1,0,0)*p_(1,0,1)+p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1)+p_(1,1,0)*p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),p_(0,0,1)*p_(1,0,0)-p_(0,0,0
       )*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p
       _(1,0,0)*p_(1,1,1),p_(0,0,0)-p_(0,0,1)+p_(0,1,0)-p_(0,1,1)+p_(1,0,0)-p_(1,0,1)+p_(1,1,0)-p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),p_(0,0,1)*p_(1,0,0)-p_(0,0,0
       )*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p
       _(1,0,0)*p_(1,1,1),p_(0,0,0)+p_(0,0,1)-p_(0,1,0)-p_(0,1,1)+p_(1,0,0)+p_(1,0,1)-p_(1,1,0)-p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),p_(0,0,1)*p_(1,0,0)-p_(0,0,0
       )*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p
       _(1,0,0)*p_(1,1,1),p_(0,0,0)-p_(0,0,1)-p_(0,1,0)+p_(0,1,1)+p_(1,0,0)-p_(1,0,1)-p_(1,1,0)+p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),p_(0,0,1)*p_(1,0,0)-p_(0,0,0
       )*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p
       _(1,0,0)*p_(1,1,1),p_(0,0,0)+p_(0,0,1)+p_(0,1,0)+p_(0,1,1)-p_(1,0,0)-p_(1,0,1)-p_(1,1,0)-p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),p_(0,0,1)*p_(1,0,0)-p_(0,0,0
       )*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p
       _(1,0,0)*p_(1,1,1),p_(0,0,0)-p_(0,0,1)+p_(0,1,0)-p_(0,1,1)-p_(1,0,0)+p_(1,0,1)-p_(1,1,0)+p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),p_(0,0,1)*p_(1,0,0)-p_(0,0,0
       )*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p
       _(1,0,0)*p_(1,1,1),p_(0,0,0)+p_(0,0,1)-p_(0,1,0)-p_(0,1,1)-p_(1,0,0)-p_(1,0,1)+p_(1,1,0)+p_(1,1,1)),
      ideal(p_(0,1,0)*p_(1,0,0)-p_(0,1,1)*p_(1,0,1)-p_(0,0,0)*p_(1,1,0)+p_(0,0,1)*p_(1,1,1),p_(0,0,1)*p_(1,0,0)-p_(0,0,0
       )*p_(1,0,1)-p_(0,1,1)*p_(1,1,0)+p_(0,1,0)*p_(1,1,1),p_(0,0,1)*p_(0,1,0)-p_(0,0,0)*p_(0,1,1)-p_(1,0,1)*p_(1,1,0)+p
       _(1,0,0)*p_(1,1,1),p_(0,0,0)-p_(0,0,1)-p_(0,1,0)+p_(0,1,1)-p_(1,0,0)+p_(1,0,1)+p_(1,1,0)-p_(1,1,1))};

m=#originalIdeals;
S=subsets(m);
#S

--for each subset construct the ideals
--append the ideal for the Zariski closure
idealsList={componentsOfTheList{I}};
for i from 1 to #S-1 list (
    --append the ideals if the set contains one element
    if(#S#i==1) then (
	currentList:=componentsOfTheList({originalIdeals#(S#i#0)});
	currentList=removeRedundantComponents(currentList);
	idealsList=append(idealsList,currentList);
	)
    --append the ideals if the set contains more than one element
    else (
	firstList := toList(set(S#i)-{last(S#i)});
	lastList := {last(S#i)};
	firstIndex := position(S,x->x==sort(firstList));
	lastIndex := position(S,x->x==sort(lastList));
	currentList = intersectLists(idealsList#firstIndex,idealsList#lastIndex);
	currentList = removeRedundantComponents(currentList);
	idealsList=append(idealsList,currentList);
	);
    print i;
    );

--remove ideals that appear several times and contain positive sums of variables
idealsList1=flatten idealsList;
idealsList2=unique(idealsList1);
idealsList3=removeRedundantComponents(idealsList2);
#idealsList3


--make likelihood ideals for each of the ideals in the list
idealsList4 = idealsList3 / (i->makeLikelihoodIdeal(i));

---------------------------
--for each likelihood ideal, the solutions can be found by the following code

loadPackage("PHCpack")

--translates p_(1,1,1) -> p_(1,1,1,1) (adds one index "1")
addIndex = (string) -> (
	addIndexString := replace(///p_\(([0-9]),([0-9]),([0-9])\)///,///p_(1,\1,\2,\3)///,string);
	return addIndexString;
	)
	
--translates p_(1,1,1,1) -> p_1111 
formatIndex = (string) -> (
	formatIndexString := replace(///p_\(([0-9]),([0-9]),([0-9]),([0-9])\)///,///p_(\1\2\3\4)///,string);
	return formatIndexString;
	)
    
--find the solutions for a likelihood ideal    
solveFromLikelihoodIdeal = (likelihoodIdeal) -> (
    R = CC[flatten entries vars ring likelihoodIdeal];
    likelihoodIdeal = sub(likelihoodIdeal, R);
    system = flatten entries gens likelihoodIdeal;
    nRing = value(formatIndex(addIndex(toExternalString(R))));
    nSystem =value(formatIndex(addIndex(toExternalString(system))));
    R = nRing;
    use R;
    system = nSystem;
    sols = solveSystem(system);
    return sols;
    )    
    
    
--ideal whose solutions we want to find    
sols = solveFromLikelihoodIdeal(idealsList4#0);



