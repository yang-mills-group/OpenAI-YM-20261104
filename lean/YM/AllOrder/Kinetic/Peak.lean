import YM.AllOrder.Kinetic.Forge
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic.Port
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a C Λ:ℝ}{k N:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)

-- ι neutral. require at least one input context. realized at scheduled Tube and full σ via graph. station choose irrelevance.
variable {ι:Type} [Nonempty ι]
variable (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ){L':ℕ}
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i))
    (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
local notation "Lℓ"=> Lobby P K G
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
set_option quotPrecheck false
local notation "A[" i "," n "]"=> clay P K (x i) p n
local notation "u[" i "," n "]"=> Lapis.orbit T[n] (F i n)

local notation "R"=> sun P K p O x L Q hx F h
variable (T:Passage P K p x Q) {i:ι}(hn:Ad G P K n)
local notation "T0" => heightV P K p Q
include Q hB hx F h T
lemma policy : Ink.Money.Code (Ad G P K) (fun i=> expand (T.inverted i) (Coarse G)) (sun P K p O x L Q hx F h) := by
 let f := knight P K p O x F; have hv(n i) : Clear (f n i):= fun k=> impulse_cost ..
 refine ⟨fun k i n hn=> ?_,fun k r i n hn=>?_⟩
 · unfold sun; rw [dif_pos hn, outbound]; let v:= faces (interiorL P K G hn); rw [Fire.once (u:=knight P K p O x F n i) _ v _ (win0 _) (hv n i)]; rfl
 let A:=rooted P K p x L Q hx F h i hn; unfold sun; simp_rw [dif_pos hn]; exact light_home (exteriorL G n) (interiorL P K G hn) _ _ A (T.inverted i) ((valuation P K p x L Q hB hx F h T hn i).2) volume (win0 _) (hv n i) r k
include hO
lemma funding (hk:k ≤ N): Apt (Ad G P K) L (snapshot (sun P K p O x L Q hx F h) k) (k+2) := by
   obtain ⟨ha,hq,hz⟩:= receipts P K p x L Q hB hx; exact settles (A:=fun i=>expand (T.inverted i) E) (gia _ hz) (fun i=> Ink.bank (T.summit i) E hz) ha (policy P K p O x L Q hB hx F h T) (fun k hk=> sunrise P K p O x L Q hB hx hO F h T hk) hk
-- total money modulo unit
-- `py` input path at arbitrary warm history. omit unnecessary witnesses
def galaxy (k:ℕ)(i:ι)(n:Side) : rule (Coarse G) n → ℝ := if hn:Ad G P K n then distilled (startup T[n] O (label S[n]) (x i) p Q hn (hx i) (h i n hn) hO) k ∘ exteriorL G n else 0
def baseStar (i:ι)(n:Side) : rule (Coarse G) n → ℝ := liftQ (clay P K (x i) p n) (fderiv ℝ (Lapis.orbit (S:=S[n]) T[n] (F i n)) 0) ∘ exteriorL G n
local notation "T'"=> baseStar P K p x F
lemma floor_at : Apt (Ad G P K) L T' 2 := by
   let f:=fun i:ι=> mote P K p (x i) 2; let H:=session P K p x Q T; have hx₁:=neophyte P K p x L Q hB hx 1 (by omega); obtain ⟨hG,hg⟩:= apex P K p x L Q hB hx T; obtain ⟨hz,hq,hv⟩:= receipts P K p x L Q hB hx; let V:= fun i:ι=> day (Coarse G) (RealSlice.Vertical G P K)
   refine Apt.adapt (Apt.move (hf:= fun i:ι=> (show Belt (V i) 1 1 from paid_day)) (gia _ zero_le_one) zero_lt_one (Apt.move hG hz hg hx₁)) (fun i n hn=>?_)
   ext1 x'; unfold mote; rw [dif_pos hn]; simp only [Function.comp_apply]; let hZ:= valuation P K p x L Q hB hx F h T hn i; let a':= T.leading i; let b':= T.inverted i
   have he:= minimum (exteriorL G n) (interiorL P K G hn) _ _ (rooted P K p x L Q hx F h i hn) a' b' (T.summit i) (T.head i) hz.le hv hZ.2 hZ.1 0 x'
   rw [show know _ n x'=mingle x' (0:rule J n) from tablet (β:=J) x']; exact he.symm
omit hB hO T in
private lemma Galaxies (i:ι)(n:Side)(hn:Ad G P K n) (x':rule E n): let g := rooted P K p x L Q hx F h i hn; let v:= interiorL P K G hn; let u:= knight P K p O x F n i; let r:=exteriorL G n; (∑ j∈range (3*k+1), outbound r v _ _ g volume u k j (mingle x' 0))= connected (castle _ _ g) volume u k (r x'):= by
    intro g v u r; have he:= posterior (u:=u) r v _ _ g volume (win0 _) k x' (fun j=> impulse_rank (fderiv ℝ (Lapis.orbit (S:=S[n]) T[n] (F i n)) 0) _ _ j); simp_rw [tablet] at he; exact he
lemma celestial (hk:k≤N): Apt (Ad G P K) L (galaxy P K p O x L Q hx hO F h k) (k+2):= by
   let v:= day (Coarse G) (RealSlice.Vertical G P K); refine Apt.adapt (Apt.move (hf:= fun i:ι=> (show Belt v 1 1 from paid_day)) (gia _ zero_le_one) zero_lt_one (funding P K p O x L Q hB hx hO F h T hk)) (fun i n hn=> ?_)
   unfold galaxy; rw [dif_pos hn]; ext1 x'; simp_rw [snapshot,sun,dif_pos hn]; simp only [Function.comp_apply,Finset.sum_apply];
   unfold v; simp_rw [tablet]; exact Galaxies P K p O x L Q hx F h i n hn x'
-- combine tape ratePlan
local notation "I"=> Ad G P K
def topiary (k:ℕ)(i:ι)(n:Side) : rule (Coarse G) n→ℝ:= galaxy P K p O x L Q hx hO F h k i n - (if k=0 then T' i n else 0)
local notation "V"=> topiary P K p O x L Q hx hO F h
lemma prism_at (hk:k≤N) : Apt (Ad G P K) L (V k) (k+2):= by
    have he:= celestial P K p O x L Q hB hx hO F h T hk; by_cases hp:k=0; subst k; exact Apt.adapt (he.add ((floor_at P K p O x L Q hB hx hO F h T).grow (show 2≤0+2 from (by omega)) |>.scale (-1))) (by intros; simp only [topiary,if_true,neg_one_smul,sub_eq_add_neg]) -- omit O later
    exact Apt.adapt he (by intros; unfold topiary; rw [if_neg hp,sub_zero])
omit T hB in
lemma actual_top (i:ι) (n:Side)(hn:Ad G P K n) (v':rule (Coarse G) n) : let A:=startup T[n] O (label S[n]) (x i) p Q hn (hx i) (h i n hn) hO; let V':=exteriorL G n; ratePlan A k (V' v')= just (preview A) k + V k i n v':= by
  intro A V'; unfold topiary galaxy ratePlan; rw [dif_pos hn]; by_cases hp:k=0; subst k; change preview A- liftQ _ _ _ + _= _; rw [if_pos rfl]; change _+distilled A 0 (V' v')= preview A+(distilled A 0 (V' v')-liftQ _ _ _); -- placeholders?
  · rw [sub_add_eq_add_sub,add_sub_assoc]; rfl
  rw [if_neg hp]; have hv(d:ℝ): just d k=0:= if_neg hp; change just _ k+ distilled A k _= just (preview A) k + ((distilled A k ((exteriorL G n) v'))-0); rw [hv,hv,sub_zero]
end YM.AllOrder.Kinetic.Port
