import YM.Integration.WilsonOriginalAlternativeStamped

/-! Ordered withdrawals on the complete original enrolled gallery. Every summand
keeps the same old physical kernel, quiet density, and all other selected ports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePorts
open Function Finset Lattice Wilson RG Marker QuadraticLocal
open WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction WilsonOriginalAlternativeHearing
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V]

def closed (c:V→Port) (vs:List V) (v:V):Port := if v∈vs then 1 else c v

def editions (c:V→Port):List V→List (V→Port)
  | []=>[]
  | v::vs=>Function.update c v 2::editions (Function.update c v 1) vs

theorem telescope (g:(V→Port)→ℂ) (s:Finset V)
    (linear:∀v∈s,∀c:V→Port,g (Function.update c v 2)=g (Function.update c v 0)-g (Function.update c v 1))
    (vs:List V) (inside:∀v∈vs,v∈s) (nd:vs.Nodup)(c:V→Port)(fresh:∀v∈vs,c v=0) :
    g c-g (closed c vs)=((editions c vs).map g).sum := by
  induction vs generalizing c with
  | nil =>
    have :(closed c [])=c:= funext fun v=>by simp [closed]
    simp [this,editions]
  | cons v vs ih =>
    simp only [editions,List.map_cons,List.sum_cons]
    have zero : Function.update c v 0 = c := by
      rw [←fresh v (List.mem_cons_self ..),Function.update_eq_self]
    have edge:=linear v (inside v (List.mem_cons_self ..)) c
    rw [zero] at edge
    have done : closed (Function.update c v 1) vs=closed c (v::vs) := by
      funext j
      by_cases p:j=v <;> by_cases q:j∈vs <;> simp [closed,p,q]
    have tail:=ih (fun j hj=>inside j (List.mem_cons_of_mem _ hj)) nd.tail (Function.update c v 1)
      (fun j hj=>by
        have h:j≠v:=fun e=>nd.notMem (e ▸ hj)
        simpa [Function.update_of_ne h] using fresh j (List.mem_cons_of_mem _ hj))
    rw [done] at tail
    rw [edge,←tail]
    abel

variable {G:Gauge} (C:Family G) {N p K f:ℕ} [Fintype V] {μ T:Type}
    (J:Census V) {W:Rep G (C.side K p)} {o:V→Site (C.side K p)}
    (A:Gallery T μ (o∘Prod.fst) W (board J))
    (F:T → Config G (C.side K p)→Poly J) (B:T → Config G (C.side K p)→V→ℂ)

theorem signed (ear:WilsonOriginalAlternativeStamped.Heard C N p K J A F B)
    (x:T)(lower:f≤K)(U:Config G (C.side f p))(s:J.Mode)
    (vs:List V)(same:vs.Perm s.val.toList):
    let g:=fun c:V→Port=>held C N p (source C p J A x c s) lower U
    held C N p (fun W'=>(F x W').part s) lower U-
      held C N p (fun W'=>(W.eval W':ℂ)*∏v∈s.val,B x W' v) lower U=
      ((editions (fun _=>0) vs).map g).sum := by
  intro g
  have hear:=ear x f lower U s
  have endpt:g (closed (fun _=>0) vs)=g (fun _=>1):=by
    have mode:(names J (closed (fun _=>0) vs)).share s=(names J (fun _=>1)).share s:=by
      apply Subtype.ext
      change s.val.image (pin (closed (fun _=>0) vs))=s.val.image (pin (fun _=>1))
      apply Finset.image_congr
      intro v hv
      have inlist:v∈vs:=same.mem_iff.mpr (Finset.mem_toList.mpr hv)
      simp [pin,closed,inlist]
    have eq:source C p J A x (closed (fun _=>0) vs) s=source C p J A x (fun _=>1) s:=by
      funext W'
      simp only [source,read_part,mode]
    dsimp only [g]
    rw [eq]
  have exchange:=telescope g s.val hear.2.2.2 vs
    (fun v hv=>Finset.mem_toList.mp (same.mem_iff.mp hv)) (same.nodup_iff.mpr (Finset.nodup_toList s.val))
    (fun _=>0) (by simp)
  rw [endpt] at exchange
  exact (congrArg₂ (·-·) hear.1.symm hear.2.1.symm).trans exchange

end YM.Integration.WilsonMeasuredPublicEntrancePorts
