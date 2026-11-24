import YM.Integration.WilsonIndependentMatchedCoverCarried

/-! Exact two-stage genealogy for the same three-color ordinary program.
Split the exterior's contraction with all old near deposits before applying
a norm. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingFirstTree
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer Outer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical

variable {G:Gauge}{i j r:ℕ}{U:Type*}
private theorem web (P:Ten ℝ U i)(Q Z:Ten ℝ U j)(r:ℕ):
    webT P (Q-Z) r=webT P Q r-webT P Z r:=by
  funext x
  by_cases h:i+j=r <;> simp [webT,h,mul_sub]

private theorem knit (P Q Z:Gen ℝ U):knitS P (Q-Z)=knitS P Q-knitS P Z:=by
  funext r
  simp only [knitS,Pi.sub_apply,web,Finset.sum_sub_distrib,swirl_mo]

private theorem block (P Q Z:Pal ℝ U):woad P (Q-Z)=woad P Q-woad P Z:=by
  funext r
  simp only [woad,Pi.sub_apply,knit,Finset.sum_sub_distrib]

theorem mixed (P Q Z:Era G ℝ):agateV P (Q-Z)=agateV P Q-agateV P Z:=by
  apply Prod.ext
  · funext i
    exact block .. 
  · exact block ..

theorem subtract (A:Levels G)(O:ChartRatio G)(N i l r:ℕ)(h:G.Simple)(g:LocalRatio O)(edge:i<N)
    (P Q Z:Era G ℝ)(p:Auth l P)(q:Auth r Q)(z:Auth r Z):
    JoinGap A O i N l r P (Q-Z)=JoinGap A O i N l r P Q-JoinGap A O i N l r P Z:=by
  unfold JoinGap
  rw [mixed,verse_lin A h edge g (p.manor q) (p.manor z),verse_lin A h edge g q z,mixed]
  abel

theorem add (A:Levels G)(O:ChartRatio G)(N i l r:ℕ)(h:G.Simple)(g:LocalRatio O)(edge:i<N)
    (P Q Z:Era G ℝ)(p:Auth l P)(q:Auth r Q)(z:Auth r Z):
    JoinGap A O i N l r P (Q+Z)=JoinGap A O i N l r P Q+JoinGap A O i N l r P Z:=by
  have he:=subtract A O N i l r h g edge P (Q+Z) Z p (q.add z) z
  rw [add_sub_cancel_right] at he
  exact (eq_add_of_sub_eq he.symm)

theorem parse (A:Levels G)(O:ChartRatio G)(N i l r n:ℕ)(h:G.Simple)(g:LocalRatio O)(edge:i<N)
    (P Q:Era G ℝ)(D:ℕ→Era G ℝ)(p:Auth l P)(q:Auth r Q)(terms:∀j<n,Auth r (D j)):
    JoinGap A O i N l r P (Q+∑j∈Finset.range n,D j)=
       JoinGap A O i N l r P Q+∑j∈Finset.range n,JoinGap A O i N l r P (D j):=by
  have entered (n:ℕ)(tr:∀j<n,Auth r (D j)):Auth r (Q+∑j∈Finset.range n,D j):=by
    induction n with
    | zero=>simpa using q
    | succ n ih=>
      rw [Finset.sum_range_succ,←add_assoc]
      exact (ih (fun j hj=>tr j (by omega))).add (tr n (by omega))
  induction n with
  | zero=>simp
  | succ n ih=>
    have before:∀j<n,Auth r (D j):=fun j hj=>terms j (by omega)
    rw [Finset.sum_range_succ,Finset.sum_range_succ,←add_assoc,add A O N i l r h g edge P _ _
      p (entered n before) (terms n (by omega)),ih before,add_assoc]

/-- At the real contact edge with the exterior, use the original product
of near means plus all and only the previously deposited pairs. -/
theorem original {e:ℕ}{E:Credit}(R:Realm G (e+1) E)(i N n l r s:ℕ)
    (span:i+1+n≤N)(P Q:ℕ→Era G ℝ)(outer:Era G ℝ)(outAuth:Auth s outer)
    (hp:∀j≤n,Auth l (P j))(hq:∀j≤n,Auth r (Q j))
    (stepP:∀j<n,verseI R.draws R.paid (i+1+j) N l (P (j+1))=P j)
    (stepQ:∀j<n,verseI R.draws R.paid (i+1+j) N r (Q (j+1))=Q j):
    let near:=cruises R.draws R.paid N (l+r) (i+1+n) (i+1) (agateV (P n) (Q n))
    let deposit j:=cruises R.draws R.paid N (l+r) (i+1+j) (i+1)
      (JoinGap R.draws R.paid (i+1+j) N l r (P (j+1)) (Q (j+1)))
    let born X:=JoinGap R.draws R.paid i N s (l+r) outer X
    born near=born (agateV (P 0) (Q 0))+∑j∈Finset.range n,born (deposit j):=by
  intro near deposit born
  have first:near=agateV (P 0) (Q 0)+∑j∈Finset.range n,deposit j:=
    WilsonIndependentMatchedCoverCarried.original R l r (i+1) N n span P Q hp hq stepP stepQ
  rw [first]
  apply parse R.draws R.paid N i s (l+r) n R.hG R.green (by omega) outer _ deposit outAuth
    ((hp 0 (Nat.zero_le _)).manor (hq 0 (Nat.zero_le _)))
  intro j hj
  have p':=hp (j+1) hj
  have q':=hq (j+1) hj
  have edge:i+1+j<N:=by omega
  apply cruising R.draws R.hG R.green (Nat.le_add_right _ _) edge.le
  exact (Auth.verse R.draws edge R.hG R.green (p'.manor q')).sub
    ((Auth.verse R.draws edge R.hG R.green p').manor (Auth.verse R.draws edge R.hG R.green q'))

end YM.Integration.WilsonSeparatedPrefixMovingFirstTree
