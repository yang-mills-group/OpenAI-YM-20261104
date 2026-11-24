import YM.MS.Orbit.Amber
/-!
# Ordinary finite lattice LPT parity and equivariance by uniqueness.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit.LogReal
open Set Filter Function Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {A W E:Type}[Fintype A]{p:Sector A}{K:Lines A}{V: Therapy A A}{U:Cog p}{ B:Series A}{Q:SpecB A}
structure PinAct (V : Op A ℂ)(p:Sector A)(K:Lines A): Prop where
   gl : Glance V
   kev (i:ℝ)(F:BL A): Cog.frame ( K i ) ( V F )= V (Cog.frame ( K i ) F)
   joins (x:ℝ)(F H: BL A): Cog.conn p ( K x ) ( V F ) ( V H )=V ( Cog.conn p ( K x ) F H )
abbrev revise (B:Series A)(V:Therapy A A):= fun k:ℕ=> V∘ B k -- replace
lemma turnQ (B X:Series A)(t:ℝ)(j k:ℕ)(h: PinAct V p K): V ( Level p K B X j k t ) = Level p K (revise B V ) (revise X V) j k t:= by unfold Level pathU; simp_rw [Finset.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i hi=>( h.joins .. ).symm
lemma pinning (h: PinAct V p K)(hp:Background p K Q B): Background p K (fun i=> V (Q i)) (revise B V):= by
   refine ⟨funext fun t=> by simp [revise,hp.1],fun i hi=>?_ ⟩ -- simp unfold
   obtain ⟨he,hV⟩:= hp.2 i hi; refine ⟨ congr_arg V he,?_⟩; apply ( Eq.mp ?_ (glpto h.gl hV) ); congr! 1; funext t; change V ((Cog.frame (K t) (B i t)) + ( ((2:ℂ)⁻¹) • (Level p K B B i 1 t) ))=_; rw [map_add,← h.kev,map_smul,turnQ _ _ t i 1 h]; rfl -- compile
lemma fixed (h:PinAct V p K)(he:Background p K Q B)(hv:∀ i,V ( Q i)=Q i)(n:ℕ)(t:ℝ): V (B n t)= B n t:= by obtain hp:= pinning h he; rw [show (fun i=>V (Q i))=Q from funext hv] at hp; exact congr_fun (congr_fun (just hp he) n) t
lemma mirrorACT (h:∀ t,U.phase (K t)): PinAct U.mirror p K := ⟨ wheel_gl U _ _, fun i=> phase_mirror (h i), fun t _ _=> phase_link (h t) ⟩ -- linter
-- sign-scale.K
omit [Fintype A] in
lemma gSign (p:Sector A): Glance (Koszul.sign p true):= by refine ⟨fun i k h=> h.signs _,fun i k t he w=>?_⟩ ; exact ( he w ).const_mul _
lemma fr_sign (V:Grain A)(F:Raw A ℂ)(hp: Clear p V): Cog.frame V ( Koszul.sign p true F )= Koszul.sign p true ( Cog.frame V F ):= by
    unfold Cog.frame; simp_rw [LinearMap.sum_apply, LinearMap.smul_apply,map_sum]; refine Finset.sum_congr rfl fun i hi=>Finset.sum_congr rfl fun j hj=>?_ ; by_cases hv:V i j=0; simp [hv]; obtain hu:=hp i j hv; rw [ diffPair_apply,sign_D,map_smul,sign_D,diffPair_apply,map_smul, ← mul_smul (cross true _ :ℂ) (cross true _ :ℂ), hu, cross_cross,one_smul ]
lemma signACT (hp:∀ t,Clear p ( K t )): PinAct (Koszul.sign p true) p K := by
    refine ⟨ gSign p, fun t F=> fr_sign _ F ( hp t ),?_ ⟩; intro t F H; simp only [Cog.conn,Koszul.link, sign_id,map_sub]; -- orientation `Koszul.times` vs product
    have he (u v:BL A): product p ( Koszul.sign p true u ) ( Koszul.sign p true v )= Koszul.sign p true (product p u v):= (.symm ( twisted_product p u v true )) -- signature
    rw [ he, fr_sign _ _ ( hp t ),fr_sign _ _ ( hp t ), fr_sign _ _ ( hp t ), he,he ]
lemma pastStand (he:Background p K Q B)(h:∀ i,Clear p (K i))(hv:∀ i:ℕ,Pure p false (Q i))(n:ℕ)(t:ℝ): Pure p false ( B n t ):= by
    have hi(i:ℕ): Koszul.sign p true (Q i)=Q i:= by rw [Pure.signs (hv i) true]; simp
    obtain hm := fixed ( V:=Koszul.sign p true ) (signACT h) he hi n t; intro l hz; obtain hx:=congr_fun hm l; simp only [at_sign] at hx; rw [show degree p l=true from (by cases ha:degree p l; exact False.elim ( hz ha ); rfl),cross_true,neg_one_mul] at hx; -- derive from add torsion
    linear_combination (norm:=ring_nf) -hx/2 -- linear ℂ.Need division.D.Op
end YM.MS.Orbit.LogReal
