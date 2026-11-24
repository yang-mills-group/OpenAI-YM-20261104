import YM.Integration.WilsonMaxwellThermometerPublicEvenSlope

/-! A true public unit on any one of the three slots contributes zero to
the signed connected coefficient at the finite position regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicUnit
open Function Finset Maxwell Maxwell.Free PowerSeries XSpace XSpace.Tornado XSpace.Normalize XSpace.Cirrus
open XSpace.Rose XSpace.Photo XSpace.Structure1 XSpace.Retirement XSpace.AxesTangent
open WilsonMaxwellThermometerPublicGalop WilsonMaxwellThermometerInteracting
open scoped BigOperators Classical
variable {G:Gauge}(W:Initialize G){V:Store G}(x:Sample 3)(p:Tags G 6 3)

theorem vacuum (e:ℕ):
    quotient W (V:=V) x p e ∅=coeff e (1:ℂ⟦X⟧):=by
  let a:Days 3:=Finsupp.single none e
  have eq (b:Days 3)(hb:b∈tally e 3)(bs:∀i:Fin 3,b (some i)=0):b=a:=by
    ext1 j
    cases j with
    | some j=> rw [bs];exact (Finsupp.single_eq_of_ne (Option.some_ne_none j)).symm
    | none=> have hk:=(totaled b).mp hb; simp_rw [Fintype.sum_option,bs] at hk;simpa [a] using hk
  have ha:a∈tally e 3:=(totaled a).mpr (by simp [a,Finsupp.single_apply])
  unfold quotient
  rw [Finset.sum_eq_single a]
  · rw [if_pos (by intro j _;exact Finsupp.single_eq_of_ne (Option.some_ne_none j)),
        glossL,show a none=e from Finsupp.single_eq_same]
  · intro b hb ne
    rw [if_neg (fun h=>ne (eq b hb (fun j=>h j (Finset.notMem_empty j))))]
  · exact fun h=>(h ha).elim

theorem withdraw (e:ℕ)(j:Fin 3)(h:p j=leaf G 6)(s:Badge):
    quotient W (V:=V) x p e s=quotient W (V:=V) x p e (s.erase j):=by
  unfold quotient
  rw [←detail,←detail]
  congr 1
  funext i
  by_cases ij:i=j
  · subst i;simp [missing,h]
  · simp [missing,ij]

theorem original (j:Fin 3)(h:p j=leaf G 6):node W (V:=V) x p=0:=by
  let v:=quotient W (V:=V) x p 0
  let w:=quotient W (V:=V) x p 1
  have v0:v ∅=1:=by simp [v,vacuum]
  have w0:w ∅=0:=by simp [w,vacuum]
  have vv (s:Badge):v s=v (s.erase j):=withdraw W x p 0 j h s
  have ww (s:Badge):w s=w (s.erase j):=withdraw W x p 1 j h s
  change first v w=0
  have paired (S T:Badge)(h:S.erase j=T):v S=v T ∧ w S=w T:=⟨(vv S).trans (congrArg v h),(ww S).trans (congrArg w h)⟩
  fin_cases j
  · have h0:= paired univ {1,2} (by decide)
    have h1:= paired {0,1} {1} (by decide)
    have h2:= paired {0,2} {2} (by decide)
    have h3:= paired {0} ∅ (by decide)
    unfold first
    rw [h0.2,h1.2,h2.2,h3.2,h1.1,h2.1,h3.1,v0,w0]
    ring
  · have h0:= paired univ {0,2} (by decide)
    have h1:= paired {0,1} {0} (by decide)
    have h2:= paired {1,2} {2} (by decide)
    have h3:= paired {1} ∅ (by decide)
    unfold first
    rw [h0.2,h1.2,h2.2,h3.2,h1.1,h2.1,h3.1,v0,w0]
    ring
  · have h0:= paired univ {0,1} (by decide)
    have h1:= paired {0,2} {0} (by decide)
    have h2:= paired {1,2} {1} (by decide)
    have h3:= paired {2} ∅ (by decide)
    unfold first
    rw [h0.2,h1.2,h2.2,h3.2,h1.1,h2.1,h3.1,v0,w0]
    ring

end YM.Integration.WilsonMaxwellThermometerPublicUnit
end
