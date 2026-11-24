import YM.AllOrder.Haiku.Low
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
open AllOrder.Haiku AllOrder.Haiku.Coat Further.PhysicalPeriodLimitF933 Shingle Macrame
variable (q:Clip) (u:ι→PathData G) (g:ι→ℝ) {b C' :ℝ}(V:ι→ℝ)(H:∀ i,(u i).Bounds q b C' (V i)) (W: ι → Towers P.L) -- namespace?
local notation "E0"=> rule (Coarse G) n
local notation "H0"=> home P K p O x L Q hx hO F h q u g
open Set
section bit
variable {G:Gauge} {c : ℕ→Side} {t b r:ℝ}
lemma trendT (d:ℝ)(he:Tendsto (fun i=> (c i).val) atTop atTop) (ht:0<r): Tendsto (fun i=> bite t r G b d (c i)) atTop (𝓝 0) := by
 let F : Side → ℝ:= fun n=>(n.val:ℝ)^12; let V:=Fintype.card (Exterior.TypeFace 1); let v:= Fintype.card G.ColorIndex
 let w:=(2:ℝ)⁻¹*((V*v:ℕ):ℝ)^2*d^2*b*t; have hv: Echo.Pulsed F:= ⟨1,12,zero_le_one,fun n=> ⟨by unfold F; positivity, (by unfold F; rw [one_mul])⟩⟩; have he':= Ink.Echo.crest hv he ht
 refine (show Tendsto (fun i=>w*(F (c i)*dearth r (c i))) atTop (𝓝 0) from (by simpa using Tendsto.const_mul w he')).congr (fun i=>?_); unfold bite Uniform.Primary; rw [Fintype.card_prod,Fintype.card_prod,site_card]; unfold w F V v dearth; push_cast; ring
lemma low_tint (v : rule (Coarse G) n) : ‖Stationary.arm G n 1 v‖ ≤ Uniform.shade G * ‖v‖:= by
 rw [portrait]; refine (Uniform.tint_le _).trans (mul_le_mul_of_nonneg_left ?_ (Uniform.shade_pos G).le); exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> norm_le_pi_norm v ((outsider G n).symm i)
end bit

def Channels (i:ι)(n:Side):=∃ m:ℕ→Side, ∃ p':ℕ→ℕ,(∀ i, Nonempty (Macrame.Window n (m i) (p' i))) ∧ (∀ i,0<p' i) ∧ Tendsto (fun i=>(m i).val) atTop atTop ∧ ∃ t r c:ℝ,0<r ∧ ∀ j, Ad G P K (m j) ∧ Gate P K p O x F q u g t r c i (m j)
variable {M₀:ℕ→ι→Ink.Field (Coarse G)} (Z':Presence P K p O x L Q hx hO F h M₀) (hey :∀ i n, Channels P K p O x F q u g i n)
include hB W hey Z' H
-- omission [Nonempty ι] invalid if theorem calls first_two etc.; include named via section undo. removed above after test
lemma clears (h':2≤N) (hG:G.Simple) : Coat.strict ((fun i j n=> (M₀ j i).table n)+ fun i=> Stipend q (u i) (g i)) 3:= by
  intro i n k hk; obtain ⟨b,C,D,hD⟩:= Z'.fee k (by omega); obtain ⟨m,p',hq,hk',hu,t,r,d,hp,hc⟩:=hey i n; let P₀ i:= (hq i).some
  let Zz(l:Side) : rule E l→ℝ:= H0 k i l; let G₀ := ((M₀ k i).table n+Stipend q (u i) (g i) k n); let s (k:ℕ):ℝ:=(p' k:ℝ)⁻¹; have hs(a:ℕ):0≤ s a:= by unfold s; positivity
  have hh(v:rule E n) : Tendsto (fun k'=> s k'* Zz (m k') (convey (P₀ k') v)) atTop (𝓝 (G₀ v)):=by
     have hx := Echo.transported P₀ (hD.awake i) (Echo.scaleLean hD.story i) hu hD.berth (dock_larger P K hB) hk' _ (Ink.LinTest.eval (k+2) v); apply (hx.add_const (Stipend q (u i) (g i) k n v)).congr; intro b; let X(b:ℕ):= convey (P₀ b) (α:=E); symm; unfold Zz home; rw [Pi.add_apply, Coat.stamina q (u i) (g i) (H i) (P₀ b)]; -- inspect
     rw [mul_add]; dsimp only [s]; rw [inv_mul_cancel_left₀ (by exact_mod_cast (hk' b).ne')]; rfl
  have hv0(v:rule E n): G₀ v=G₀ 0:= by
      let R(k:ℕ):= Zz (m k) (convey (P₀ k) v) - Zz (m k) 0;
      -- R →0 via Gate.0 etc
      have hw: Tendsto R atTop (𝓝 0):= by
        by_cases hK:k=2; swap; · refine tendsto_const_nhds.congr' (Eventually.of_forall fun i=>?_); rw [show R i=0 from sub_eq_zero.mpr (first_two P K p O x L Q hx hO F h q u g V H W (hc i).2 (hc i).1 (by omega) hG _ _)] -- typo
        subst k; let y:= Uniform.shade G*‖v‖; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero (fun k=> norm_nonneg _) (fun i'=>?_) (trendT (b:=t) (G:=G) (t:=d) y hu hp); exact second_fee P K p O x L Q hx hO F h q u g W (hc i').2 (hc i').1 _ ((low_tint (convey (P₀ i') v)).trans (mul_le_mul_of_nonneg_left (Ink.Echo.amounts ..) (Uniform.shade_pos G).le))
      refine sub_eq_zero.mp (tendsto_nhds_unique (hh v|>.sub (hh (0:rule E n))) (?_))
      have hs' : Tendsto (fun i=> s i*R i) atTop (𝓝 0):= by
          apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero (fun i=> norm_nonneg _) (fun i=> ?_) (show Tendsto (fun i=> ‖R i‖) atTop (𝓝 0) from tendsto_zero_iff_norm_tendsto_zero.mp hw); rw [norm_mul]; refine mul_le_of_le_one_left (norm_nonneg _) ((Real.norm_of_nonneg (hs i)).trans_le (inv_le_one_of_one_le₀ ?_)); exact_mod_cast (show 1 ≤ p' i from hk' i)
      refine hs'.congr (fun i=>?_); unfold R; rw [mul_sub]; change _= s i*_ - s i*Zz _ (convey _ 0); rw [map_zero]

  exact fun x y=> Eq.trans (hv0 x) (hv0 y).symm
end YM.AllOrder.Kinetic.Port
