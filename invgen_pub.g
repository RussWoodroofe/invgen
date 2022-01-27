#======================================================
# The following functions use a variant of the segmented sieve
#  of Eratosthenes.  In each segment, it calculates the prime
#  numbers.  It also calculates the largest prime-power divisor
#  of each number in the segment if less than the segment size,
#  or otherwise records the segment size in place of the largest
#  prime power divisor.
# Finding the primes and largest factors in a segment is much
#  faster than checking each number directly.
#======================================================

# lists of primes, non-prime prime-powers, and largest pp divisors
invgen_smallpps:=[];
invgen_smallpp_primes:=[];
invgen_primes:=[];
invgen_ppdivs:=[];
# scratch variable used for keeping track of divisors
invgen_partlyfactored:=[];

# variables to keep track of which segment we're in
invgen_segsize:=0;
invgen_segcurrent:=0;

# marker to place in invgen_ppdivs for numbers with a prime power divisor > segsize
invgen_bigppmarker:=0;

# Perform a direct sieve on the initial segment, and set up some other bookkeeping details
InvgenKnowPpDivisorsSegmentedInit:=function(n)
  local i,j;

  invgen_segsize:=RootInt(n-1)+1;

  # preallocate memory for the list of primes (+ a little extra)
  invgen_smallpps:=EmptyPlist(Int(invgen_segsize/LogInt(invgen_segsize,3))+100);
  invgen_primes:=EmptyPlist(Int(invgen_segsize/LogInt(invgen_segsize,3))+100);
  invgen_ppdivs:=List([1..invgen_segsize], x->1);
  invgen_partlyfactored:=List([1..invgen_segsize], x->1); # allocate memory only

  invgen_segcurrent:=0;
  invgen_bigppmarker:=invgen_segsize+1;

  for i in [2..invgen_segsize] do
    if invgen_ppdivs[i] = 1 then
      AddSet(invgen_primes, i);
    fi;
    if invgen_ppdivs[i] = 1 or (RemInt(invgen_ppdivs[i], i / invgen_ppdivs[i]) = 0) then
      AddSet(invgen_smallpps, i);
      j:=1;
      while i*j <= invgen_segsize do
        invgen_ppdivs[i*j]:=i;
        j:=j+1;
      od;
    fi;
  od;

  # get list of primes associated with small pps
  invgen_smallpp_primes:=List(invgen_smallpps, SmallestRootInt);
end;

# compute the primes, prime-powers, and largest pp divisors in a segment
InvgenKnowPpDivisorsInSegment:=function(segment)
  local i,j, pp, p, seg_zero, seg_end, ppos, ini, fin;

  if segment >= invgen_segsize or segment < 0 or not IsInt(segment) then
    Info(InfoWarning, 1, "WARNING: InvgenKnowPpDivisorsInSegment called with illegal segment number ", segment);
    return fail;
  fi;

  # we look at the numbers from segsize*segment + 1 to segsize*(segment+1)
  seg_zero:= invgen_segsize*segment;
  seg_end:=seg_zero+invgen_segsize;

  # we need to know primes from the prior segment (for the last 1-2 from the segment)
  #  compute them if if necessary
  if segment > 0 then
    if segment=invgen_segcurrent+1 then
      i:=invgen_primes[Length(invgen_primes)];
      j:=invgen_primes[Length(invgen_primes)-1];
    else
      i:=PrevPrimeInt(seg_zero+1);
      j:=PrevPrimeInt(i);
    fi;
  fi;
  invgen_segcurrent:=segment;

  invgen_primes:=EmptyPlist(Int(invgen_segsize/LogInt(invgen_segsize,3)/2)+100);
  if segment > 0 then
    AddSet(invgen_primes, j);
    AddSet(invgen_primes, i);
  fi;

  # assume invgen_ppdivs is already initialized to the right length; overwrite with 1's
  CopyListEntries([1],1,0,invgen_ppdivs,1,1,invgen_segsize);
  CopyListEntries([1],1,0,invgen_partlyfactored,1,1,invgen_segsize);

  # Look for known small pp divisors (<= invgen_segsize)
  for i in [1..Length(invgen_smallpps)] do
    pp:=invgen_smallpps[i];
    p:=invgen_smallpp_primes[i];

    # mark off entries divisible by pp.
    ini:=(QuoInt(seg_zero, pp) + 1)*pp - seg_zero;
    fin:=(QuoInt(seg_end,pp))*pp - seg_zero;
    for j in [ini,ini+pp..fin] do
      invgen_ppdivs[j]:=pp;
      invgen_partlyfactored[j]:=invgen_partlyfactored[j]*p;
    od;
  od;

  for i in [1..invgen_segsize] do
    # did we find any factors at all?  If not, it's prime
    if invgen_partlyfactored[i] = 1 then
      Add(invgen_primes, seg_zero + i);
      invgen_ppdivs[i]:=seg_zero+i;
    # are we missing some factors?  If all factors are small,
    #   we should have invgen_partlyfactor[i] = seg_zero + i
    elif invgen_partlyfactored[i] <= seg_zero then
      invgen_ppdivs[i]:=invgen_bigppmarker; # standin for a big prime power divisor
    fi;
  od;

  # prime calculation will be off for segment 0, so cheat and copy from small_pp_primes
  if segment=0 then
    invgen_primes:=Set(invgen_smallpp_primes);
  fi;
  MakeImmutable(invgen_primes);
end;

# Test routine, returns the primes through n
InvgenKnowPrimesThrough:=function(n)
  local i, primes;
  primes:=[];
  InvgenKnowPpDivisorsSegmentedInit(n);
  primes:=ShallowCopy(invgen_primes);
  for i in [1..invgen_segsize-1] do
    InvgenKnowPpDivisorsInSegment(i);
    UniteSet(primes, invgen_primes);
  od;
  return primes;
end;

#======================================================
# The following functions are utility functions for checking
#  a generated subgroup is not imprimitive or intransitive
#======================================================

# simplify and make more specific the PrevPrimeInt function from GAP
#  returns greatest prime <= n and >= lowest (or fail if there is none such)
#  does not assume that our sieve is pointed at the range containing n
invgen_preveqp_wheel:=[2,fail,2,fail,4,fail,6,fail,2,fail,4,fail,2,
                      fail,2,fail,4,fail,2,fail,2,fail,4,fail,2,fail,4,fail,6];
InvgenPrevOrEqPrimeInt:=function(n, lowest)
  if n < 3 then
    n:=2;
  elif n mod 2 = 0 then
    n:=n-1;
  fi;
  while n >= lowest and not IsPrimeInt(n) do
    n:=n-invgen_preveqp_wheel[(n mod 30)];
  od;
  if n<lowest then
    return fail;
  fi;
  return n;
end;

# Check whether n is a power of q
#   Repeatedly dividing by q is faster than CoefficientsQadic
InvgenIsQPowerInt:=function(n,q)
  local k;
  k:=n;
  while k mod q = 0 do
    k:=k/q;
  od;
  return (k=1);
end;

# pre-compute the prime power divisors of numbers up to 100
invgen_ppdivint_cache:=List([ [  ], [ 2 ], [ 3 ], [ 2, 4 ], [ 5 ], [ 2, 3 ], [ 7 ], [ 2, 4, 8 ], [ 3, 9 ],
  [ 2, 5 ], [ 11 ], [ 2, 3, 4 ], [ 13 ], [ 2, 7 ], [ 3, 5 ], [ 2, 4, 8, 16 ],
  [ 17 ], [ 2, 3, 9 ], [ 19 ], [ 2, 4, 5 ], [ 3, 7 ], [ 2, 11 ], [ 23 ],
  [ 2, 3, 4, 8 ], [ 5, 25 ], [ 2, 13 ], [ 3, 9, 27 ], [ 2, 4, 7 ], [ 29 ],
  [ 2, 3, 5 ], [ 31 ], [ 2, 4, 8, 16, 32 ], [ 3, 11 ], [ 2, 17 ], [ 5, 7 ],
  [ 2, 3, 4, 9 ], [ 37 ], [ 2, 19 ], [ 3, 13 ], [ 2, 4, 5, 8 ], [ 41 ],
  [ 2, 3, 7 ], [ 43 ], [ 2, 4, 11 ], [ 3, 5, 9 ], [ 2, 23 ], [ 47 ],
  [ 2, 3, 4, 8, 16 ], [ 7, 49 ], [ 2, 5, 25 ], [ 3, 17 ], [ 2, 4, 13 ], [ 53 ],
  [ 2, 3, 9, 27 ], [ 5, 11 ], [ 2, 4, 7, 8 ], [ 3, 19 ], [ 2, 29 ], [ 59 ],
  [ 2, 3, 4, 5 ], [ 61 ], [ 2, 31 ], [ 3, 7, 9 ], [ 2, 4, 8, 16, 32, 64 ],
  [ 5, 13 ], [ 2, 3, 11 ], [ 67 ], [ 2, 4, 17 ], [ 3, 23 ], [ 2, 5, 7 ], [ 71 ],
  [ 2, 3, 4, 8, 9 ], [ 73 ], [ 2, 37 ], [ 3, 5, 25 ], [ 2, 4, 19 ], [ 7, 11 ],
  [ 2, 3, 13 ], [ 79 ], [ 2, 4, 5, 8, 16 ], [ 3, 9, 27, 81 ], [ 2, 41 ], [ 83 ],
  [ 2, 3, 4, 7 ], [ 5, 17 ], [ 2, 43 ], [ 3, 29 ], [ 2, 4, 8, 11 ], [ 89 ],
  [ 2, 3, 5, 9 ], [ 7, 13 ], [ 2, 4, 23 ], [ 3, 31 ], [ 2, 47 ], [ 5, 19 ],
  [ 2, 3, 4, 8, 16, 32 ], [ 97 ], [ 2, 7, 49 ], [ 3, 9, 11 ], [ 2, 4, 5, 25 ] ], Immutable);

InvgenPrimePowerDivisorsInt:=function(n)
  if n <= Length(invgen_ppdivint_cache) then
    return invgen_ppdivint_cache[n];
  else
    # our pre-computed values will handle most cases.
    Info(InfoWarning, 1, "InvgenPrimePowerDivisorsInt called with large value ", n);
    return Filtered(DivisorsInt(n), x->IsPrimePowerInt(x));
  fi;
end;

# Check whether n and k have the right form for k to be the size of a
#  fixed point set of a primitive action by PSL on n elements
InvgenHasPSLActWithFixed:=function(n,k)
  local q, bad;

  # In the PSL(d,q) case, n = (q^d - 1)/(q-1) and k = (q^j - 1)/(q-1) for j <= d/2
  # in this case, n-1 and k-1 are both divisible by q.
  bad:=false;

  for q in InvgenPrimePowerDivisorsInt(GcdInt(n-1,k-1)) do
    if InvgenIsQPowerInt(k*(q-1)+1,q) and InvgenIsQPowerInt(n*(q-1)+1,q) then
      bad:=true;
      break;
    fi;
  od;
  return bad;
end;

# The following trial division routine is slightly faster than FactorsInt if all
#   prime factors are fairly small, and doesn't alloc memory
invgen_2ndlargestpp:=1;
InvgenLargestPpFactor:=function(n)
  local m, p, currentpp, largestpp;

  m:=n;
  largestpp:=1;
  invgen_2ndlargestpp:=1;
  for p in invgen_primes do
    if m mod p = 0 then
      currentpp:=1;
      repeat
        m:=m/p;
        currentpp:=currentpp*p;
      until m mod p <> 0;
      if currentpp > largestpp then
        invgen_2ndlargestpp:=largestpp;
        largestpp:=currentpp;
      elif currentpp > invgen_2ndlargestpp then
        invgen_2ndlargestpp:=currentpp;
      fi;
      if m=1 then
        return largestpp;
      fi;
    fi;
  od;
  # shouldn't reach here if m>1, shouldn't be called with m=1
  Info(InfoWarning, 1, "Ran out of primes in InvgenLargestPpFactor with ", n);
  return largestpp;
end;

# look for a carry in base-p multiplication
#   (avoids systems of imprimitivity w p-power element)
InvgenProductHasNoCarry:=function(n, d, p)
  return (Maximum(ProductCoeffs(CoefficientsQadic(n/d, p),CoefficientsQadic(d,p))) < p);
end;

# find the cycle structure of a p-power element in S_n with the fewest cycles
#   not currently called by main routines, kept for utility
InvgenMTCycleStruc:=function(n, p)
  local i, basep, digit, rc;

  basep:=CoefficientsQadic(n,p);
  digit:=1;
  rc:=[];
  for i in [1..Length(basep)] do
    Append(rc, ListWithIdenticalEntries(basep[i], digit));
    digit:=digit*p;
  od;
  return rc;
end;

# Return true if p divides Binomial(i,j).  Equivalent to not having
#  base-p cycle structure element of i fixing a set of size j
PrimeDividesBinomialLucas:=function(i,j,p)
  local id, jd;

  # Only compute as many qadic digits as we need
  id:=i;
  jd:=j;

  while jd > 0 do
    if RemInt(id, p) < RemInt(jd, p) then
      return true;
    fi;
    id := QuoInt(id, p);
    jd := QuoInt(jd, p);
  od;
  return false;
end;

#  Check if A_n has no intransitive sg with maximal-orbitted
#    pp and rp elements
#  Assume called with p divisor of n, r > sqrt(n)
InvgenIsPrimitive:=function(n,p,r)
  local porbits, rorbits, c, k, gcd, pcycstruc, i, j, s;

  # first look for a possible system of imprimitivity
  #   this may be redundant with the below, but it is
  #   also quick to check and eliminates some failures

  # number of r-cycles
  c:= QuoInt(n,r);

  # number of fixed points by r-elt
  k:= n - c*r;

  # first, look for a possible system of imprimitivity
  gcd := GcdInt(c, k);
  if gcd > 1 then
    if RemInt(gcd,p)=0 then return false; fi;

    if Number(DivisorsInt(gcd), x->InvgenProductHasNoCarry(n, x, p)) > 1 then
      return false;
    fi;
  fi;

  # now, look for a partition of intransitivity
  #   use that intransitivity of sgs generated by given r- and p-power-cycles is
  #   equivalent to intransitivity of sgs generated by associated Sylow sgs
  for i in [0..QuoInt(c,2)] do
    for j in [0..k] do
      s := i*r + j;
      if s>0 and not PrimeDividesBinomialLucas(n,s,p) then
        return false;
      fi;
    od;
  od;
  return true;
end;

# Look for product of r-cycles that generates together with a base-p element
# Passed: maxrange (an upper bound on the numbers listed), smoothnumbers
#   (a list of numbers to check), snpp (a parallel array of the largest pp divisors)
# It expected that the list in smoothnumbers consists of the numbers failing the
#  "easy" test from [Shareshian/Woodroofe:2018].
InvgenCheck_PhaseTwo:=function(maxrange, smoothnumbers, snpp)
  local failingnumbers, p, p2, pp, p2p, i, n, good, k, c, r, minr, count;
  if invgen_segsize < Log2Int(maxrange)^2*10 then
    InvgenKnowPpDivisorsSegmentedInit(maxrange);
    invgen_segcurrent := -1;
  fi;

  # we want the initial segment of primes loaded for trial division in InvgenLargestPpFactor
  if invgen_segcurrent <> 0  then
    InvgenKnowPpDivisorsInSegment(0);
  fi;

  failingnumbers:=[];
  for i in [1..Length(smoothnumbers)] do
    n := smoothnumbers[i];
    good := false;

    # largest prime-power factor was stored in first pass.  Find 2nd largest, and associated primes
    pp := snpp[i];
    p2p := InvgenLargestPpFactor(n / pp);  # n is fairly smooth, so trial division is efficient
    p := SmallestRootInt(pp);
    p2 := SmallestRootInt(p2p);

    # Don't use 2 as a prime divisor in this situation, as the 2-order element with largest
    #  orbits sometimes still has smaller orbits than the Sylow sg
    if p = 2 then p:=p2; pp:=p2p; p2:=2; fi;
    if p2 = 2 then
      p2p := invgen_2ndlargestpp; # calculated in InvgenLargestPpFactor
      p2 := SmallestRootInt(p2p);
      if p2 = 1 then
        Info(InfoWarning, 1, "Ran out of odd prime factors in InvgenCheckInRange with ", n);
      fi;
    fi;

    # find a prime close to n/c for a small c.
    # We'll need to show that we're not in a proper primitive subgroup
    #   Excluding a few small cases, we need only worry about
    #   A_b acting on pairs (which we avoid by taking c < sqrt(n/2))
    #   and PSL acting on points from the Liebeck/Saxl list.
    # Checking transitivity and non-imprimitivity is more straightforward

    # As very small values of c should often work, we try those first
    for c in [2..QuoInt(pp,2)] do
      r:=InvgenPrevOrEqPrimeInt(QuoInt(n-3,c), QuoInt(n-pp,c)+1);

      if r=fail or InvgenHasPSLActWithFixed(n,n - c*r) then continue; fi;
      if InvgenIsPrimitive(n,p, r) or (r*c + p2p > n and InvgenIsPrimitive(n, p2, r)) then
        good:=true;
        break;
      fi;
    od;

    # if small c didn't work, then give up and completely factor n-k for small k's
    minr:=2*RootInt(n);  # we could make a slightly smaller value of r work, but shouldn't need it
    k:=3;
    while not good and k < pp do
      if not InvgenHasPSLActWithFixed(n, k) then
        r:=Maximum(FactorsInt(n-k));
        if r >= minr then
          if InvgenIsPrimitive(n, p, r) or (k < p2p and InvgenIsPrimitive(n, p2, r)) then
            good:=true;
          fi;
        fi;
      fi;
      k:=k+1;
    od;

    if not good then
      AddSet(failingnumbers, n);
    fi;

  od;
  return failingnumbers;
end;

invgen_oversmooth:=[];
invgen_oversmooth_range:=[];
InvgenCheckPhaseTwoFromFilesInDirectory:=function(passed)
  local path, filename, files, slashpos, failingnumbers, num_failing, totalchecked, starttime;
  files:=[];
  totalchecked:=0;
  starttime:=Runtime();

  if IsString(passed) then
    path := UserHomeExpand(passed);
    if path[Size(path)] <>  '/' then
      Append(path, "/");
    fi;
    if IsReadableFile(path) then
      for filename in DirectoryContents(Directory(path)) do
        if StartsWith(filename, "out-") and EndsWith(filename, ".g") then
          AddSet(files, Concatenation(path, filename));
        elif StartsWith(filename, "out-") and EndsWith(filename, ".g.gz") then
          AddSet(files, Concatenation(path, filename{[1..Size(filename)-3]}));
        fi;
      od;
    fi;
  else
    Info(InfoWarning, 1, "Unrecognized argument");
    return fail;
  fi;

  Print("Checking Phase 2 on ", Size(files), " files\n");
  failingnumbers:=[];
  num_failing:=0;
  for filename in files do
    invgen_oversmooth:=[];
    invgen_oversmooth_range:=[];
    Read(filename);
    if invgen_oversmooth_range = [] then
      Info(InfoWarning, 1, "Unexpected content found in ", filename);
    fi;
    Print(" ", Size(invgen_oversmooth), " numbers in the range ",
          invgen_oversmooth_range, " from ",  Last(SplitString(filename, "/")), "\n");
    UniteSet(failingnumbers, InvgenCheck_PhaseTwo(Last(invgen_oversmooth_range),
           List(invgen_oversmooth, First), List(invgen_oversmooth, Last)));
    if (Size(failingnumbers) > num_failing) then
      Print(" --> ", Size(failingnumbers) - num_failing," failing number(s) found\n");
      num_failing:=Size(failingnumbers);
    fi;
    totalchecked:=totalchecked+Size(invgen_oversmooth);
  od;
  Print("Checked ", totalchecked, " numbers in ", StringTime(Runtime() - starttime),".\n");
  return failingnumbers;
end;

# Check invariant generation by two prime-power order elements for all
#  n between l and m.
# This is mostly superseded by a combination of C code and postprocessing by
#  InvgenCheckPhaseTwoFromFilesInDirectory
InvgenCheckInRange:=function(larg, m)
  local l, bigprime, primes_num, bigprime_pos, n, i, smoothnumbers, snpp, good,
        c, r, p, pp, p2, p2p, segzero, segend, failingnumbers;

  # avoid trivial cases
  l:=Maximum(larg,25);

  Print("\rBeginning computation: numbers ", l, " through ", m, "     \n\c");

  # initialize segmented prime and pp divisors sieve
  InvgenKnowPpDivisorsSegmentedInit(m);
  segend:=0;  # know ppdivs in correct segment the first time through main loop

  # find the largest prime that is less than l
  #  (keeping this updated allows us to avoid repeatedly searching invgen_primes)
  bigprime:= InvgenPrevOrEqPrimeInt(l-3, 2);

  # initialize list of smooth numbers (failing phase 1)
  #   with a guess at how much space we'll need to allocate
  smoothnumbers:=EmptyPlist(Int(invgen_segsize*4/5));
  snpp:=EmptyPlist(Int(invgen_segsize*4/5));

  ####
  # apply the easy test first, which anyway works with density 1:
  ####
  Print("Phase 1:  filter sufficiently non-power-smooth numbers\n\c");
  for n in [l..m] do
    # update segment of ppdivs, if necessary
    if n>segend then
      InvgenKnowPpDivisorsInSegment(QuoInt(n-1,invgen_segsize));
      bigprime_pos:=PositionSet(invgen_primes, bigprime);
      segzero:=invgen_segcurrent*invgen_segsize;
      segend:=segzero+invgen_segsize;
      primes_num:=Length(invgen_primes);
      if (RemInt(invgen_segcurrent,100)=99) then
        Print("\rExamining segment ", invgen_segcurrent+1, " / ", invgen_segsize, "     \c");
      fi;
    fi;

    #   Look for an r-cycle which overlaps with a maximally transitive p-power element
    #   This works for the same reasons as [Shareshian/Woodroofe:2018].
    if not (bigprime + invgen_ppdivs[n-segzero] > n) then

      # By [Jones:2014], a cycle fixing 2 points is in a primitive subgroup
      #  only when n-1 is a prime power.  Of course, if n-2>2 is prime, then n-1 is even
      #  In this case, we can use n-2 as our bigprime
      if not (2^Log2Int(n-1) = n-1 ) and bigprime_pos < primes_num and n-2 = invgen_primes[bigprime_pos+1] then
        # pass test with r = n-2 instead of r = bigprime
      else
        Add(smoothnumbers, n);
        Add(snpp, invgen_ppdivs[n-segzero]);

        # sanity check -- make sure we don't have our bigpp marker
        #  (It would be highly surprising to find an interval [n - sqrt(m), n] with no prime!)
        if invgen_ppdivs[n-segzero] = invgen_bigppmarker then
          Info(InfoWarning, 1, "Unexpectedly passing non-smooth number on to Phase 2: ", n);
        fi;
      fi;
    fi;

    # update bigprime
    if bigprime_pos < primes_num and n-2 = invgen_primes[bigprime_pos+1] then
      bigprime:=n-2;
      bigprime_pos:=bigprime_pos+1;
    fi;
  od;

  Print("\r                                        \r");

  ####
  # Now apply the hard tests to the (few) numbers that remain:
  # We look for a prime r, so that r^2 < n, and so that for c = floor(n/r), we have
  #  c*r + p^a > n.  [Liebeck/Saxl:1985] allows checking the generated subgroup is not
  #  primitive.  Transitive is handled by Lucas' theorem.  Imprimitive is more delicate.
  ####
  Print("Phase 2:  find mid-sized primes r for ", Length(smoothnumbers), " power-smooth numbers\n\c");

  failingnumbers:=InvgenCheck_PhaseTwo(m, smoothnumbers, snpp);

  return failingnumbers;
end;
