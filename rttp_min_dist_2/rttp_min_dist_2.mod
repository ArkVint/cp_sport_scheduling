
using CP;
int nbTeams = ...;
range rngTeams = 1..nbTeams;
int nbRounds = ...;
range rngRounds = 1..nbRounds;
range Where=0..2;
int bbye=0;
int home=1;
int away=2;

int nbTeamGames = ...;

int M[rngTeams][rngTeams]=...;
int D[rngTeams,rngTeams]=...;
int HAP[rngTeams,rngRounds]=...;
int PR[rngTeams,1..nbTeamGames]=...;
int NativeSolution[rngTeams,rngRounds]=...;
int TeamsDist[rngTeams]=...;


dvar int x[rngTeams,rngRounds] in 0..nbTeams;
dvar int v[rngTeams][0..nbRounds+1] in rngTeams;

execute{
  writeln("Defining search strategy and setting parameters");
  cp.param.TimeLimit = 3*60;
  var f=cp.factory;
 
  var phase1 = f.searchPhase(x, f.selectSmallest(f.domainSize()),
                  f.selectLargest(f.value()));
  var phase2 = f.searchPhase(v, f.selectSmallest(f.domainSize()),
                  f.selectLargest(f.value()));
 
 
 /*
  var phase1 = f.searchPhase(x);  
  var phase2 = f.searchPhase(v);
 */
  cp.setSearchPhases(phase1, phase2);
  
  cp.param.PresolveLevel=6;
  cp.param.Workers = 4;
  cp.param.AllDiffInferenceLevel = 6;
  cp.param.CountInferenceLevel = 6;
  
}

dexpr int seqCount = sum(g in 1 .. nbTeamGames-1, t in rngTeams) (x[t][PR[t][g]] == x[t][PR[t][g+1]]);
dexpr int distance = sum(i in rngTeams, r in 0..nbRounds)D[v[i][r],v[i][r+1]];


//minimize sum(i in rngTeams, r in 0..nbRounds)D[v[i][r],v[i][r+1]];
//minimize staticLex(distance, seqCount);
minimize distance;
subject to
{ 
   
   forall(r in rngRounds, t in rngTeams) {
      x[t,r] != t;
   };
	       	
   forall (r in rngRounds, t1 in rngTeams, t2 in rngTeams: t2 != t1)
      (x[t1,r] == t2) == (x[t2,r] == t1);
      
   forall (r in rngRounds, t in rngTeams)
      HAP[t,r] == bbye => x[t,r] == 0;
      
      /*
   forall ( r in rngRounds, t1 in rngTeams: HAP[t1,r] == home, t2 in rngTeams : t2 != t1)
   	  x[t1,r] == t2  => HAP[t2,r] == away;
   	  
   forall ( r in rngRounds, t1 in rngTeams : HAP[t1,r] == away, t2 in rngTeams : t2 != t1)
   	  x[t1,r] == t2  => HAP[t2,r] == home;   	
    */
    
   forall ( r in rngRounds, t1 in rngTeams, t2 in rngTeams : t2 != t1)
   	  x[t1,r] == t2 && HAP[t1,r] == home => HAP[t2,r] == away;
   	  
   forall ( r in rngRounds, t1 in rngTeams, t2 in rngTeams : t2 != t1)
   	  x[t1,r] == t2 && HAP[t1,r] == away => HAP[t2,r] == home;
   	
    forall (t1 in rngTeams, t2 in rngTeams : t2 != t1) 
    sum(r in rngRounds) (x[t1,r] == t2 && HAP[t1,r] == home) == M[t1][t2];
  
  forall (t1 in rngTeams, t2 in rngTeams : t2 != t1) 
  	sum(r in rngRounds) (x[t1,r] == t2 && HAP[t1,r] == away) == M[t1][t2];
  
  //sum(g in 1 .. nbTeamGames-1, t in rngTeams) (x[t][PR[t][g]] == x[t][PR[t][g+1]]) <= 8;

  //Set venues
   forall (r in rngRounds, t in rngTeams : HAP[t,r] != bbye)  {
   	 HAP[t,r] == home  => v[t][r] == t && v[x[t,r]][r] == t; 
   	 HAP[t,r] == away  => v[t][r] == x[t,r] && v[x[t,r]][r] == x[t,r];
   };
    
  //Start and finish at home
  forall(t in rngTeams){
    v[t][0] == t;
    v[t][nbRounds+1] == t;
  }
  
  //Stay at the same venue during a bye
  forall(r in rngRounds, t in rngTeams)
    x[t][r] == 0 =>  v[t][r] == v[t][r-1];
    
   
  
   forall(t in rngTeams){
  		sum( r in 0..nbRounds) D[v[t][r],v[t][r+1]] <= TeamsDist[t];    
   }
  
 }   
  	
	
main
{
		thisOplModel.generate();
		var sol=new IloOplCPSolution();
		for(var t in thisOplModel.rngTeams)
			for(var r in thisOplModel.rngRounds)
				sol.setValue(thisOplModel.x[t][r], Opl.abs(thisOplModel.NativeSolution[t][r]));
	    cp.setStartingPoint(sol);  
		cp.solve();
		thisOplModel.postProcess();
	  
}

int res[t in rngTeams, r in rngRounds]=
(HAP[t,r]==home)?(x[t][r]):
((HAP[t,r]==away)?(-x[t][r]):0);

execute
{
 writeln(res);  
}
   