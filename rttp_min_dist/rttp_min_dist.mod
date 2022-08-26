
using CP;
int nbTeams = ...;
range teams = 1..nbTeams;
int nbRounds = ...;
range rounds = 1..nbRounds;
int M[teams][teams]=...;
int D[teams,teams]=...;
int HP[teams,rounds]=...;
int AP[teams,rounds]=...;

dvar int x[teams][teams][1..nbRounds] in 0..1;
dvar int v[1..nbTeams][0..nbRounds+1] in 1..nbTeams;

execute{
  writeln("Defining search strategy and setting parameters");
  cp.param.TimeLimit = 2*60;
  var f=cp.factory;
  var phase1 = f.searchPhase(x, f.selectSmallest(f.domainSize()),
                  f.selectLargest(f.value()));
  var phase2 = f.searchPhase(v, f.selectSmallest(f.domainSize()),
                  f.selectLargest(f.value()));
  cp.setSearchPhases(phase1, phase2);
  cp.param.PresolveLevel=6;
  cp.param.Workers = 4;
  cp.param.AllDiffInferenceLevel = 6;
  cp.param.CountInferenceLevel = 6;
}


minimize sum(i in teams,r in 0..nbRounds)D[v[i][r],v[i][r+1]];
subject to
{  
  //All matches
  forall(i,j in teams)
    sum(r in 1..nbRounds) x[i][j][r] == M[i][j];

    
  forall(i in teams, r in 1..nbRounds)  
    count(append(all(j in teams: j != i)x[i][j][r], all(j in teams)x[j][i][r]), 1) <= 1;
  
  forall(i in teams, r in rounds)
  	  sum(j in teams: j != i) x[i][j][r] == HP[i][r];
  	  
    forall(j in teams, r in rounds)
  	  sum(i in teams: j != i) x[i][j][r] == AP[j][r]; 	  
  
    
  //Set venues
  forall(i,j in teams, r in rounds)
    x[i][j][r] == 1 => v[i][r] == i  && v[j][r] == i;
  
  //Start and finish at home
  forall(i in teams){
    v[i][0] == i;
    v[i][nbRounds+1] == i;
  }
  
  //Stay at the same venue during a bye
  forall(i in teams, r in rounds)    
    sum(j in teams) (x[i][j][r]+x[j][i][r]) == 0 => v[i][r] == v[i][r-1];
 
}