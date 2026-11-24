import YM.WilsonCoeffUV.Stable.Analytic.Budget
import YM.WilsonCoeffUV.Marked.Capture.Earned
/-! # Captured source: exact full kernel into (exponential!) persistent analytic stable class

Bridge both sectors. Use weighted polynomial cap independently on soft reports, this is for relative
moment losses through calibration windows in S2.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.StableStrip
open Wheel Wheel.Mark Wheel.Flooring Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Next.Foundations Real Shard Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q u:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G} {B z:ℝ}{E W W' V' X Y K:Credit}
-- twig kme au demand conversion for projection. allow all the presentations. Cost absorbed by same-stage costs on L,V.
lemma projected (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W:Credit):∃ X:Credit,∀ L:Theatre H T p e E W, ∀ (m:ℕ)(ha:L.V.anchor≤m)(Y:TowerS G D)(A:ℝ),0≤ A→(∀ i≤e,∀ j,Twig 0 (lampp L m ha) A (Y.2 i j))→∀ i≤e,∀ x:Alma F, ‖coeff i (opal F Y x)‖≤ L.V.cash X m*A:=by
    let B (i:ℕ):= (billingQ (Hooks G) i (h*h)).usingC W; let z:=coinQ F (le_refl (h*h)) D
    obtain ⟨X,hX⟩:=uniformPays (P:=fun i X=>∀ y,1≤y→(B i).buy y≤X.buy y) (Finset.range (h+1)) (fun i _=>⟨B i,fun _ _=>le_rfl⟩) (fun _ _ _ _ h p x v=> (p x v).trans (h x v)); refine ⟨(pur z).prodC X,?_ ⟩
    intro L m g Y A hp hv i w x; rw [cash,Credit.products]; let P:= L.V.cash X m; let C:= P*A; let y:=L.V.y m; have he:= L.V.depth _ g
    have hx j t (r:j≤ e)(p:t≤ h): YieldP 0 1 (h*h) C 1 (Y.2 j t) (Y.2 j t):=by
        apply YieldP.same _ zero_le_one; have he':= twig_Offer (k:=h*h) (G:=G) le_rfl (hv j r t) (L.angle m g).lamp.positive (W.purchase he) (L.spend m g).cap
        apply he'.more; rw [mul_comm]; exact mul_le_mul_of_nonneg_right ((Credit.stock_up (billingQ (Hooks G) t (h*h)) W _).symm.le.trans (hX _ (Finset.mem_range.mpr (by omega)) _ he)) hp
    have ht : ‖glean F Y.2 i x‖ ≤ z*(P*A):=(foreQ (e:=e) 1 zero_le_one F (le_refl (h*h)) (fun i j p r=> hx i j p r) x w).main
    rw [opal,coeff_mk,mul_assoc]; apply ht.trans; exact mul_le_mul_of_nonneg_right (pure_goal z _) (mul_nonneg (zero_le_one.trans (X.purchase he)) hp)
lemma stripInit (H:Hol G)(T:SectionData F)(p:h<D)(e k:ℕ)(E W:Credit):∃ X: Credit,∀ L:Theatre H T p e E W,∀ (m N:ℕ)(ha:L.V.anchor≤ m)(_hm:m ≤ N)(Y:TowerS G D)(A:ℝ),0≤ A→ h≤k →On k Y →(∀ i ≤ e,∀ j,Twig 0 (lampp L m ha) A (Y.2 i j)) → stripHeight F e k (lampp L m ha) (L.V.cash X m * A) (Silt (L.lore N m) Y):=by
   obtain ⟨S,hS⟩:=projected H T p e E W
   obtain ⟨V,hV⟩:=allPlays H T p e E W
   let P:ℕ:=Fintype.card (Alma F)*(e+1); let X:= Credit.unit.plus ((pur P).prodC (S.prodC V))
   refine ⟨X,fun L m N ha hm Y A z g h t=>?_⟩
   obtain ⟨x,y⟩:= sifted _ (production L hm ha).1 h g; let u:=L.V.y m; have hu:1≤u:=L.V.depth _ ha; let H':=V.buy u; have he:= (S.purchase hu).trans' zero_le_one; have hg:0 ≤ H':= zero_le_one.trans (V.purchase hu)
   have hh:0≤ L.V.cash X m * A:= mul_nonneg (zero_le_one.trans (X.purchase hu)) z
   refine ⟨x,y,hh,fun i r w=>?_⟩
   have ht v (q:v ≤ i) (j:Alma F): Cork Bank.terrain 0 (lampp L m ha) H' ((L.lore N m).2 j v r):= ((cheers L (hV v (valence F j) r (q.trans w)) ha hm le_rfl j rfl).wax)
   refine Cork.cost (Cork.sub (t i w r) (inkAr (j:=i) (opal F Y) (L.lore N m) (L.angle m ha).lamp.positive.le (fun j x=>hS L m ha Y A z t j (x.trans w)) ht hg)) ?_
   refine le_trans ?_ (mul_le_mul_of_nonneg_right (Credit.fuel _ _ hu) z); rw [Credit.unit_cost,Credit.products,Credit.products,add_mul,one_mul]; apply add_le_add_right
   exact (mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr (Nat.mul_le_mul_left (Fintype.card (Alma F)) (show i+1≤ e+1 by omega))).trans (pure_goal P u)) (mul_nonneg (mul_nonneg he z) hg)).trans (le_of_eq (by unfold H' u; ring))

lemma crest_le_one (A:Levels G)(m:ℕ)(p:5≤ A.clock.J (m+1)): crestM A m p≤1:=by
    have he:= cue_unit (G:=G) (K:=A.clock.kernel) (A.clock.adm m) p
    let a:=A.clock.J m; let b:=A.clock.J (m+1); refine (spatter G A.clock.kernel a b (A.clock.adm _) p).2.le.trans ((min_le_left ..).trans ?_); unfold Tokenizer.outlet; linarith only [he]

-- price B polynomial Z exp through soft. no older report precision from this alone.
theorem received (H:Hol G)(T:SectionData F)(p:h<D)(e k:ℕ)(Q: Fin (a+1)→ SealR G)(E W V' X W0 E' W' K:Credit)(B:ℕ) : ∃ C Y: Credit,∀ (L:Theatre H T p e E W) (P:Realm G (e+1) E') (_u:RootDeal L k K) (_v:Tribe P H W0 V' Q)(_s:L.V.draws=P.draws)(_t:L.V.paid=P.paid)(_w: L.V.y=P.y)(m b j N:ℕ)(hb:P.anchor≤ b)(pb:L.V.anchor≤ j)(hz:j≤ b)(_h:b≤m)(_hq:m≤ N) (ψ: Wilt Q) (f:Fin (a+1)→ℝ)(Z:Herit Q)(ρ z :ℝ)(l:5≤ P.draws.clock.J (b+1)),
    (P.mint b hb).σ=crestM P.draws b l → (lampp L b (pb.trans hz)) ≤ crestM P.draws b l → Cloze (fun i=>(Q i).D) (asp Q) P W'→ capP Q≤k →PadRank P b m z → galeGate G (fun i=>(Q i).D) (asp Q) (asp Q) e (dictated H Q E' W0 V' X e).choose W' E' z ≤ρ →Shipfit P.draws.S Q ψ m b ρ z f B → (∀ i,sprouted (Q i) (Z i) e (X.buy z)) →∀ i ≤ e,∀ r,
     let F0:= AutumnDay L.V.draws L.V.paid ψ Z m b N D
     let R:=breaths L.V.draws L.V.paid T p N k b j (Silt (L.lore N b) F0)
     Twig 0 (lampp L j pb) (L.V.cash Y j*L.V.tempC j b*(exp (C.buy z)*(∏ i, f i))) (R.2 i r):=by
   obtain ⟨V,hV⟩:= invoke H Q e E' W0 V' X W' B; obtain ⟨U,hU⟩:= stripInit H T p e k E W
   obtain ⟨Y,hY⟩:= exponentialStable H T p e k E W K
   refine ⟨U.plus V, Y,?_⟩; intro L P q x s t w m b j n g h v z a' ψ f Z ρ y ℓ A θ hC hq KP hp hs he i w' r F0 R
   let W0':=Vσ P b g; let I:=∏ i,f i; let B:= exp (V.buy y)*I; have hI:0≤I:=Finset.prod_nonneg (fun i _=> (hs.amp i).1)
   have hF:F0=AutumnDay P.draws P.paid ψ Z m b n D:=by unfold F0; rw [s,t]
   have ht:On k F0:= hF.symm ▸ GatesC (H:=H) (R:=P) (W:=W0) (V':=V') (fun i=>⟨(x i).prest⟩) ψ Z g z a' hq
   let s':=lampp L b (h.trans v); have hg:s'≤ W0':= θ.trans_eq (by unfold W0' Vσ; rw [A,min_eq_right (crest_le_one ..)])
   have hy:=KP.year b le_rfl z; have hpos:=P.depth _ g; let C:=L.V.cash U b; have hh0:=hU L b n (h.trans v) (z.trans a') F0 B (mul_nonneg (exp_pos _).le hI) q.dom ht (fun i w r=> hF.symm ▸ (Cork.mono (hV P x m b n z a' g ψ f Z ρ y D hC KP hp hs he i w r) hg)); apply Cork.cost (hY i w' r L q _ h b n v (z.trans a') (Silt (L.lore n b) F0) _ hh0)
   apply mul_le_mul_of_nonneg_left _ (mul_nonneg (zero_le_one.trans (Y.purchase (L.V.depth _ h))) (trail_pos ..).le); change C*B≤_
   unfold B; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hI; apply le_trans (mul_le_mul_of_nonneg_right (_ : C ≤ exp (U.buy y)) (exp_pos _).le); · rw [← exp_add]; exact exp_le_exp.mpr (Credit.fuel _ _ (hpos.trans hy))
   unfold C cash; rw [w]; apply le_trans (U.elder hpos hy); linarith only [add_one_le_exp (U.buy y)]
end YM.WilsonCoeffUV.StableStrip
