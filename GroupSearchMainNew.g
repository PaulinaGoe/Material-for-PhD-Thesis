

# " Check whether the degree of the character x is a square integer larger than 1  ";
# " Input: a character x; Output: a truth value ";

IsSquareDeg := function(x) 
	return (DegreeOfCharacter(x) > 1 and IsSquareInt(DegreeOfCharacter(x)));
end;

# " Check whether character factorises on two subgroups H and K of a group G for an irrep chi";
# "Input: group G, character chi, subgroups H and K; Output: truth value";

FactorisingCharacter := function(chi, G, H, K)
	local h,k;
	for h in Elements(AsSubgroup(G,H)) do 
		for k in Elements(AsSubgroup(G,K)) do
			if (((k^chi)*(h^chi))/DegreeOfCharacter(chi) <> (k*h)^chi) then
				return false;
			fi;
		od;
	od;
	return true;
end;

# "Check if two subgroups commute";
# "Input: group G, subgroups H and K; Output: truth value";

CommutingSubgroups := function(G,H,K)
		local h,k;
		for h in GeneratorsOfGroup(AsSubgroup(G,H)) do
			for k in GeneratorsOfGroup(AsSubgroup(G,K)) do
				if h*k <> k*h then
					return false;
				fi;
			od;
		od;
		return true;
end;

# " Build list of subgroups such that character restricted to subgroup decomposes as a single irrep with multiplicity equal to dimension";
# "Input: a list of subgroups SG, character chi; Output: lsit of subgroups of G";

TestCharacter := function(SG,x)
	local H, chi, output;
	output := [];;
	for H in SG do
		chi := RestrictedClassFunction(x,H);
		if (DegreeOfCharacter(chi) = DegreeOfCharacter(x) and IsCharacter(chi/Sqrt(DegreeOfCharacter(x))) and IsIrreducible(chi/Sqrt(DegreeOfCharacter(x))))
				then Add(output, H);
		fi;
	od;
	if Length(output) < 4 then
		return fail;
	fi;
	return output;
end;

# "Function that tests if agiven element is in a given set";
# "Input: Element, Set; Output: truth value"

IsInSet := function(Element, Set)
	local t;
	for t in Set do
		if t = Element then
			return true;
		fi;
	od;
	return false;
end;

# "Find triplets such that the first two elements form an element in the first and the second list, and the third together with the second, and the third together with the first,";
#" are in the second list but not in the first list.";
# "Input: List1, List2; Output: list of triplets or fail";

FindTriplets := function(List1, List2)
	local Element1, Element2,Output;						
				
	Output := [];;

	for Element1 in List1 do 
		for Element2 in List2 do
			if (Element1[2] <> Element2[2] and Element1[1] = Element2[1]) then
				if (IsInSet([Element1[2],Element2[2]], List2) or IsInSet([Element1[2],Element2[2]], List2)) then 
						#"check that triplet is not already in the output list";	
						if (IsInSet([Element1[1],Element1[2],Element2[2]], Output) or IsInSet([Element1[2],Element1[1],Element2[2]], Output)) = false then 
							Add(Output, [Element1[1],Element1[2],Element2[2]]);
						fi;
				fi;	
			elif (Element1[1] <> Element2[1] and Element1[2] = Element2[2]) then
				if (IsInSet([Element2[1],Element2[1]], List2) or IsInSet([Element1[1],Element2[1]], List2)) then
						#"check that triplet is not already in the output list";
					if (IsInSet([Element1[1], Element1[2],Element2[1]], Output) or IsInSet([Element1[2],Element1[1],Element2[1]], Output)) = false then 								Add(Output, [Element1[1],Element1[2],Element2[1]]);
					fi;
				fi;
			fi;
		od;
	od;
	if Length(Output) =0 then
		return fail;
	fi;
	return Output;
end;

#" This function sorts a list of subgroups into to lists of pairs of subgroups: one in which the subgroups are quasi-orhtogonal and commute with each other and one in which";
#" the subgroups are quasi-orthogonal but do not commute with each other. Moreover, the function updates the memory list of commuting subgroups.";
#"Input: a list of subgroups SGList, a character chi, a list of subgroups that commute (the memory); Output: two lists or fail";

SortSubgroups := function(SGList, chi,G, MemorySG)
 		local Output1, Output2, H, K, flag;
		Output1 := [];
                Output2 := [];
                for H in SGList do
                       for K in SGList do
                               if K<>H then
                                    flag := true;
                                    # " Check if pair is already in memory, if not adjust flag and check if pair commutes";
                                    if (IsInSet([H,K], MemorySG) or IsInSet([K,H], MemorySG)) = false then
                                                 flag := false;
                                                 if CommutingSubgroups(G, H, K) then
                                                              Add(MemorySG, [H,K]);
                                                              flag := true;
                                                 fi;
                                    fi;
                                    # "Divide into list of quasi-orth and commuting and quasi-orth and non-commuting pairs";
                                    if FactorisingCharacter(chi, G, H, K) then
                                                     if flag = true then 
							Add(Output1, [H,K]);
                                                     else
                                                        Add(Output2, [H,K]);
                                                     fi;
                                    fi;
                               fi;
                       od;
                od;
		# "Return fail if lists are emptyor too short";
		if (Length(Output1) <2 or Length(Output2) <2) then
			return fail;
		fi;
		return [Output1, Output2];

end;



#"This function is the main function which tests if a given group G satisfies the desired criteria (check out the dissertation for more details).";
#" Input: group G; Output: a list containing a group G, a character degree and a number of subgroup triplets, or fail";

TestGroup := function(G)
	local x, Triplets, MemorySG, Results, SG, SGChi, flag, H, K, SGQuasiOrthComm, SGQuasiOrthNonComm;
	#"First compute all subgroups of G and store them in a list:";
	SG := List(ConjugacyClassesSubgroups(G), H -> Representative(H));
	#"Memory that stores commuting subgroups:";
	MemorySG := [];;
	#" Loop through all irreps of G and filter out candidate irreps ";
	for x in Irr(G) do 
		if IsSquareDeg(x) then
			# "Build list of subgroups fulfilling character condition";
			SGChi := TestCharacter(SG,x);
			if SGChi <> fail then
				#"Sort the subgroups into quasi-orthogonal commuting and quasi-orthogonal and non-commuting pairs:"; 
				if SortSubgroups(SGChi, x, MemorySG, G) <> fail then
					SGQuasiOrthComm:= SortSubgroups(SGChi, x , MemorySG)[0];
					SGQuasiOrthNonComm := SortSubgroups(SGChi, x, MemorySG)[1];
				fi;
				# "Find Triplets";
				Triplets := FindTriplets(SGQuasiOrthComm, SGQuasiOrthNonComm);
				if (Triplets <> fail and IdSmallGroup(G) <> fail) then
					Print("Group:", IdSmallGroup(G), "\n", "Irrep:", DegreeOfCharacter(x), "\n", "Number of Subgroup Triplets:", Length(Triplets), "\n");
					return [G, DegreeOfCharacter(x), Length(Triplets)];
				fi;
			fi;
		fi;
	od;
	return fail;
end;


" Build list of groups to test  ";
groups := Flat(List( [1152..1152] , j -> List( [2..NrSmallGroups(j)], i -> SmallGroup(j,i)))); 

" ...or just a single one. This one should be accepted. ";
groups1 := [SmallGroup(243,65)];


counter := 0;
for G in groups do
	if TestGroup(G) <> fail then
		counter := counter + 1;
		Print(TestGroup(G));
	fi;
od;

Print("Number of successes: ", counter, "\n");
                                                                                                                                  
