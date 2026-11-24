import YM.OPE.Compatible.Gum.Oath
/-!
# All trace accounts, ordinary torque identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
-- accounting index and oriented trans
local notation "Q!"=> Active G (forest S.ratio he)
local notation "S!"=> Bid.Dir G c × AxisChart G X!
open Flume.Script Shell
local notation "T!"=> Flume.Script.Tile G S.ratio.count
open Planned.PrimaryIntegral295.Carrier
local notation "CAX" => actLight S he H G
def Litlock (p:Script T! i) : Prop:= ∀ k:Kv,∀ x:Fin i→ S!, library c p (dance S he G ∘ (DoubleX S he H k ∘ x))= library c p (dance S he G ∘ x)
lemma canvas (v:Kv)(x:J!): DoubleX S he H v (InV S he H G x)=InV S he H G x:=Prod.ext (map_zero (AnalyticNext.QuarticMatch.Joint.shifts (G:=G) (axisK v) (offset v c))) (echoRot ..)
private lemma fixed_slot {α E B : Type*} [DecidableEq α] (T : E ≃ B) (W : E → E)
    (F : (α → B) → ℝ) (hF : ∀ z, F (T ∘ (W ∘ z)) = F (T ∘ z))
    (q : α → B) (i : α) (v v' : E) (hv : W v = v')
    (rest : ∀ j, j ≠ i → W (T.symm (q j)) = T.symm (q j)) :
    F (Function.update q i (T v')) = F (Function.update q i (T v)) := by
  let z := Function.update (T.symm ∘ q) i v
  have base : T ∘ z = Function.update q i (T v) := by
    funext j
    by_cases h : j = i <;> simp [z, h]
  have moved : T ∘ (W ∘ z) = Function.update q i (T v') := by
    funext j
    by_cases h : j = i
    · subst j; simp [z, hv]
    · simp only [Function.comp_apply, z, Function.update_of_ne h, rest j h, Equiv.apply_symm_apply]
  exact (congrArg F moved.symm).trans ((hF z).trans (congrArg F base))

private lemma fixed_coordinates {ι E : Type*} [Fintype ι] [AddCommMonoid E] [Module ℝ E]
    (b : ι → E) (W : E → E) (N : Matrix ι ι ℝ) (l : E →ₗ[ℝ] ℝ) (F : ι → ℝ)
    (hN : Nᵀ = N) (coords : ∀ i, W (b i) = ∑ j, N j i • b j)
    (fixed : ∀ i, l (W (b i)) = l (b i)) (values : ∀ i, l (b i) = F i) :
    N *ᵥ F = F := by
  funext i
  change (∑ j, N i j * F j) = F i
  rw [← values i, ← fixed i, coords, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ← values j]
  exact congrArg (· * l (b j)) (congrFun (congrFun hN j) i)

private lemma four_average {ι : Type*} [Fintype ι] (N : Kv → Matrix ι ι ℝ)
    (M : Matrix ι ι ℝ) (F : ι → ℝ) (comm : ∀ t, N t * M = M * N t)
    (fixed : ∀ t, N t *ᵥ F = F) :
    (((∑ t, N t) * M) *ᵥ ((1/4 : ℝ) • F)) = M *ᵥ F := by
  have hcomm : (∑ t, N t) * M = M * (∑ t, N t) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => comm t
  rw [hcomm, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.sum_mulVec]
  simp_rw [fixed]
  rw [Finset.sum_const, Finset.card_univ, kvCard]
  congr 1
  ext1 j
  change (1/4 : ℝ) * (4 • F j) = F j
  rw [nsmul_eq_mul]; push_cast; ring

private lemma twirl_basis (w : Kv) (i : Q!) :
    twirlF S he H w ((countingBasis X! G) i) =
      ∑ j : Q!, (leanI S he H G w) j i • (countingBasis X! G) j := by
  let m := countingBasis X! G
  let N := leanI S he H G w
  let y : Z! := twirlF S he H w (m i)
  change y = ∑ j : Q!, (N j i) • m j
  rw [← m.sum_equivFun y]
  apply Finset.sum_congr rfl; intro j _; congr! 1; exact (bill_def ..).symm

private lemma ward_rotates {r : ℕ} (f : Script T! r) (Y : S!) (x : J!)
    (i : Fin r) (q : Fin r → deck T! c) (m' : Kv) (x' : Z!)
    (hQ : ∀ j, j ≠ i → q j = dance S he G Y + CAX x ∨ q j = dance S he G Y)
    (fixed : DoubleX S he H m' Y = Y) (hx : Litlock S he H f) :
    library c f (Function.update q i (dance S he G (0, twirlF S he H m' x'))) =
      library c f (Function.update q i (dance S he G (0, x'))) := by
  let W := DoubleX S he H m' (G:=G)
  refine fixed_slot (paintV S.ratio he G).toEquiv W (library c f) (hx m') q i
    (0, x') (0, twirlF S he H m' x') ?_ ?_
  · exact Prod.ext (map_zero (AnalyticNext.QuarticMatch.Joint.shifts (G:=G) (axisK m') (offset m' c))) rfl
  · intro j hh
    rcases hQ j hh with ha|hb
    · have hp : (paintV S.ratio he G).symm (q j) = Y + InV S he H G x :=
        (paintV S.ratio he G).symm_apply_eq.mpr (by rw [map_add]; exact ha)
      change W ((paintV S.ratio he G).symm (q j)) = (paintV S.ratio he G).symm (q j)
      rw [hp, map_add, show W Y = Y from fixed, show W (InV _ _ _ _ x) = _ from canvas S he H ..]
    · change W ((paintV S.ratio he G).symm (q j)) = (paintV S.ratio he G).symm (q j)
      rw [show (paintV S.ratio he G).symm (q j) = Y from (paintV S.ratio he G).symm_apply_eq.mpr hb,
        show W Y = Y from fixed]

private lemma pile_contract (P w : Flume.Script.Tab T! c → ℝ) (q : Q! → ℝ)
    (zero : ∀ j : Flume.Script.Tab (Shade G) c, P (starI j) = 0)
    (active : ∀ j, P (pileV S he G j) = q j) :
    ∑ j, P j * w j = ∑ j, q j * w (pileV S he G j) := by
  rw [sumBoard]
  simp_rw [zero, zero_mul, Finset.sum_const_zero, zero_add]
  rw [← (squad S.ratio he G).sum_comp]
  exact Finset.sum_congr rfl fun j _ => congrArg (· * w (pileV S he G j)) (active j)

include t h hc in
private lemma ward_active_sum (w : Flume.Script.Tab T! c → ℝ) (k : Q!)
    (invariant : ∀ v : Kv, leanI S he H G v *ᵥ (fun j => w (pileV S he G j)) = (fun j => w (pileV S he G j))) :
    ∑ j : Flume.Script.Tab T! c, Oriel C CAX (pileV S he G k) j * (1/4 * w j) =
      ∑ j : Flume.Script.Tab T! c, (Piax S G U).acts c (pileV S he G k) j * w j := by
  let u := pileV S he G
  let K := SUMp S he H G
  let M := (FUND S he U)⁻¹
  let F (j : Q!) := w (u j)
  calc
    _ = ∑ j : Q!, (K*M) k j * (1/4 * F j) :=
      pile_contract S he (fun j => Oriel C CAX (u k) j) (fun j => 1/4 * w j) _
        (fun j => (cam_nil S he H (C:=C) j _).2) (fun j => camIs S he H U t h hc k j)
    _ = ∑ j : Q!, M k j * F j :=
      congrFun (four_average (fun j => leanI S he H G j) M F (fun j => leanKi S he H U t h j) invariant) k
    _ = _ :=
      (pile_contract S he (fun j => (Piax S G U).acts c (u k) j) w _
        (fun j => (piax_nil S U j _).2) (fun j => planeR S he U t h k j)).symm

include S he H G A U L h K g t hc C
-- probe r tail invariant implies Wick col.
set_option maxHeartbeats 200000 in
lemma wardlock {r:ℕ}(f:Script T! r)(p:Keys G (Limb H))(hf:Summable f)(hx:Litlock S he H f): Rookie C CAX (Piax S G U) (dance S he G (fieldT (cabin g) (cloak H p))) f (1/4:ℝ):=by
       let T:= dance S he G; let Y:= fieldT (cabin g) (cloak H p)
       intro i x q hQ k
       rcases pile_or S he k with ⟨k,rfl⟩|⟨k,rfl⟩
       · apply Finset.sum_congr rfl; intro j _; rw [show Oriel C CAX (starI k) j=0 from (cam_nil S he H (C:=C) k j).1]; erw [(piax_nil S U k j).1,zero_mul, zero_mul]
       let L(p:Flume.Script.Tab T! c):=library c f (Function.update q i (deltaH p)); let m:= countingBasis X! G; let u:=pileV S he G; let F(j:Q!):= L (u j); let D:= listV f c; let v: Z!→ℝ:= fun y=>library c f (Function.update q i (T (0,y))); have hp(j):v (m j)= F j:=by unfold v F L; erw [(dawn S he U t h A.pays).token];rfl
       have hv:∃ V: Z!→ₗ[ℝ] ℝ, v=V:=by let V:= D.toContinuousLinearMap q i; refine ⟨(V ∘L T ∘L ContinuousLinearMap.inr ℝ _ _).toLinearMap,funext fun x=>?_⟩;exact (muses f hf _).symm
       obtain ⟨l,hl⟩:=hv
       have he₁ (m' : Kv) (x' : Z!) : v (twirlF S he H m' x') = v x' :=
         ward_rotates S he H f Y x i q m' x' hQ (knowV S he H U h t ..) hx
       have hF (m' : Kv) : leanI S he H G m' *ᵥ F = F := by
         apply fixed_coordinates (fun j => m j) (twirlF S he H m') _ l F (leanEq S he H m')
         · exact twirl_basis S he H m'
         · intro i; rw [← congrFun hl, ← congrFun hl]; exact he₁ m' (m i)
         · intro i; rw [← congrFun hl]; exact hp i
       exact ward_active_sum S he H U t h hc L k hF
end YM.OPE.Cascade.Rill
