import YM.Contacts.Revest.Outlay
import YM.MergeProof.Almandine
/-! latch forecasts from ANY paid Factor. W not repinned here. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Revest
open AnalyticBridge VerifiedReset Collection Flute Outlay
open PhysicalNext.Repeat PhysicalNext.Repeat.Roost Terrain
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Org
open UVNext.CouplingReset Push.AbsoluteSums Animals Precision RG.Supply Input RG.Shoot PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Next.Scheduling PhysicalNext.ThroughLaunch Time Model Arbor Province.Costing Tucks Milling.Steam Pressure
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{l q r v t d D' μ s:ℝ}
namespace Anthem
-- unit forecast stake for k,n against same Leg.H
variable {M:Metals G} {D:Rolls M.p} {B:Alloy M D}(A:Factor B){N m n i j k:ℕ}
-- IMPORTANT expand notation in variable declarations From Purity.B
set_option quotPrecheck false
local notation "x" => B.B.a.clock.hatBeta m
local notation "y" => B.B.a.clock.hatBeta (m+1)
local notation "J" => B.B.a.clock.J (m+1)
local notation "I" => B.B.a.clock.J m
local notation "σ" => B.B.a.params m
local notation "p" => B.B.a.budget m
local notation "S" => B.B.a.S.side m n
local notation "Ω" => quoteHard B.B.a m A.book
local notation "γ" => B.B.a.clock.allowance m
local notation "α" => B.B.kin.alpha N m
local notation "K" => B.B.kin.path N m

-- assumes clocks for invocation. late criterion ν_F. for use at x
abbrev Steady (G: Gauge) (p':Stage) (t:ℝ) (d:ℝ) (k i :ℕ) := ∀ m:Side,∀ (B: BudgetPoint)(Q:PathData G)(F:bore G),Time.Same p' B→10*B.B < m.val→(∀ i₀≤k,Charted G k t B Q F p'.clip d (ripe t) ε₀ i₀ i)→ ∀ u∈Icc ((1/4:ℝ)*t) (4*t), ∀ v∈Icc ((1/4:ℝ)*t) (4*t), let T:=integrated (n:=m) B F p'.clip Q k; Flute.Salary B (T u) (ν t) ∧ Flute.Salary B (T u-T v) (|u-v| *t^(-(43/20):ℝ))
lemma registry (G:Gauge) (K₀:ℕ)(f:Stage) : ∀ᶠ X:ℝ in atTop,∀ (d:ℝ)(j:ℕ), Steady G f X d K₀ j:= (baker (G:=G) K₀ f (1/4) 4 (by norm_num)).mono fun X hX d j m B T F hp ht=> hX m B T F hp ht d (ripe X) j
variable (g:G.Simple) {F:bore G} (hk:∀ i'≤k,Charted G k (B.B.a.clock.hatBeta m) (B.B.a.budget m) (B.B.kin.path N m) F (B.B.a.params m).clip d (ripe (B.B.a.clock.hatBeta m)) ε₀ i' i)
    (hu:Anthem.Steady G (B.B.a.params m) (B.B.a.clock.hatBeta m) d k i)
    (hB: Bargain G (B.B.a.params m) (A.book (B.B.a.clock.J (m+1)) (B.B.a.clock.J m)) (A.scout (B.B.a.clock.J (m+1)) (B.B.a.clock.J m)) (B.B.a.clock.hatBeta m) (B.B.a.clock.hatBeta (m+1)) (UVNext.CouplingReset.alphaBound D (B.B.a.clock.J (m+1))))
    (hw:10*(B.B.a.budget m).B < (B.B.a.S.side m n).val) (hm:m<N)
variable {U:Rep G (B.B.a.S.side (m+1) n)}(hb:U.beta∈ band B.B.a (m+1))(hU:Lives B.B.bake N (m+1) n U)
    {C:Listing G (B.B.a.S.side m n)}{V: Collection.Source G (B.B.a.S.side m n)}
local notation "Y" => integrated (n:=S) p F (σ).clip K k (U.beta+q)
local notation "C₀" => (shelves C K p)
local notation "T₀" => Hybrid.pliant C K (σ).clip p V q
local notation "Δ" => delta (C.read V)
local notation "Z" => U.beta+q+Δ
local notation "τ" => (vac V t)
local notation "Y'" => integrated (n:=S) p F (σ).clip K k Z
local notation "T" => Flute.put (Flute.put (C₀) p) p
local notation "P'" => Flute.lay Y' (Flute.lay (Y-Y') T₀)
-- Inv. x.t β. don't shadow in notation var declarations
structure Truth {G:Gauge} {f:Side} (Q:RG.Rep G f)(k:ℕ)(F:bore G) (c:ℝ) (s:ℝ) :Prop where
   cost : ∃ X:Poetry.Lecturer Q Q.p.B, Terrain.Toll Q (Poetry.unknown X) s c ∧ ∀ u,Q.activities.E (X.place u)=integrated (B:=Q.p) F Q.clip Q.path k Q.beta u -- NOTE s implicit; make explicit

include g A hm hB hw hk hu hU hb
lemma publishes (ht:Collection.Local C p V v (forecastK B.B.a m A.scout U.beta)) (ha:|q-α| ≤ potion x)
    (hf:v ≤ forecastE B.B.a m/4) (hv:∀ V':Config G S, earlyValue C K (σ).clip p V (U.beta+q) t 0 V' * Real.exp (layer (fun d : Low => d.loan K (σ).clip 0 p q 0) V') *Real.exp (- Flute.film p Y V')=(B.B.a.clock.op m n).push U.beta U.eval V'):
    let r:=finish K (σ).clip p T P' Z (τ); B.B.Move N m n r U ∧ (p).threshold^2 *|r.beta-(U.beta+q)|≤v ∧ Truth r k F (s:=γ) (brutal σ G*v):= by
    let b:= (p); let V₀:= v; have hs:Time.Same σ b:= ⟨rfl,rfl,rfl⟩; obtain ⟨hc,h₀,hz,hh,h,hE,hK⟩:= hB.doctor b hs (Deployment.clock_eqns B.B.a.clock m|>.2.2.2.2.2.2) rfl U.beta α q v Δ hb (UVNext.CouplingReset.within_alpha («B»:=B.B) hm) ha hf (delta_bound g ht.projects); let Q:= Z; obtain ⟨hM,-⟩:=hu _ _ _ _ hs hw hk Q (hz Δ le_rfl) _ (hz Δ le_rfl); have hw':U.beta+q∈ Icc _ _:=(add_zero (U.beta+q)) ▸ hz 0 (by rw [abs_zero]; positivity); obtain ⟨-,hr⟩:= hu _ _ _ _ hs hw hk _ hw' _ (hz Δ le_rfl)
    obtain ⟨Hx,H',X,h,H⟩:= Purity.prizes A g hm hU hb ht (Tucks.grow hr h) hM hv hK hc h₀ hh
    intro r
    obtain ⟨b,h',hV,hS⟩:=h.wage; have ht:0≤γ:=(by change 0≤ δE x; unfold δE Clock.gap; positivity); exact ⟨Hx,H',⟨X,⟨b,h',fun i=>Cost.enlarge (hV i) (hh.trans (by change (γ)/32≤γ; linarith)), hE ▸ hS⟩, H⟩⟩
-- positivity proof ht mixing; fix
end Anthem
end YM.Contacts.Revest
