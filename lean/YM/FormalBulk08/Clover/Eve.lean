import YM.FormalBulk08.Clover.Surf
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Clover
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{E m n l e r j t d D R:ℕ}{X I:Type}
variable {J U:X→ℕ}{F:∀ x:X,Flight (J x) (U x)}{V:∀ x:X,Lodge (F x).patch}{H:∀ x,(F x).patch.Branches K G}{Z L:∀ i:X,Train (J i)}{τ:Time X}{σ η δ g μ:X→ℝ}
variable {hL:∀ i,2≤(F i).L.val}{o:Loc G 1}{B:Frame G d}{W Y:X→ Pot G}{T S A: X→Plaza B D}{ρ:ChartRatio G}{a:hue G}

-- omit constituents from RHS estimate: use direct isolated single column
-- transport. U not synthetically prepriced when slots match & weight up.
def Nextpay (o:Loc G 1)(τ:Time X)(σ η μ g:X→ℝ)(r:ℕ)(T S:X→ Studio D →Tile (edgeL G) r):Prop:= ∃ V:X→ℝ,Soft τ V∧(∀ i,0≤V i) ∧ ∀ x A, 0≤A→ (∀ p,Knoxville (fame _) (σ x) (0,o) (T x p) (A*‖p‖))→ ∀ p, Knoxville (fame _) (η x) (0,o) (S x p) ((μ x*A + V x*g x)*‖p‖)
-- e unused: drop
lemma earns {D:Type*}{K:Reach D}{p:D}{v x:Tile D n}{η A B c:ℝ}(h: Knoxville K η p (c • v+x) A)(hx: Knoxville K η p x B)(hc:1≤ c): Knoxville K η p v (A+B):= by -- V dummy
   have hz:=penn_sub h hx; rw [add_sub_cancel_right] at hz; have he:= hz.smul c⁻¹; have ht:0<c:= lt_of_lt_of_le zero_lt_one hc; rw [inv_smul_smul₀ ht.ne'] at he; exact he.mono (mul_le_of_le_one_left hz.1 (by rw [abs_of_pos (inv_pos.mpr ht)]; exact inv_le_one_of_one_le₀ hc))
lemma nextsolve {T S Y W: X→ Studio D→Tile (edgeL G) r} {b:X→ℝ}(h: Nextpay o τ σ η μ g r T S)(hp:Tender τ o η g W)(he:∀ i p,S i p=b i • Y i p+ W i p)(h':∀ i,1≤b i): Nextpay o τ σ η μ g r T Y:= by
    obtain ⟨V,hV,P,H⟩:=h; obtain ⟨B,b,U,L⟩:=hp; refine ⟨_,hV.plus b,fun i=>add_nonneg (P i) (U i),fun x A hA Ht p=>?_⟩; have he':= H x A hA Ht p; rw [he] at he'; apply Knoxville.mono (Clover.earns he' (L x p) (h' x)); apply le_of_eq;ring
lemma crown_weight (L:Side)(x:Letter B):1 ≤heightK L d (Pose.weight B x):= by rw [heightK_of_le L (weightFits ..)];apply one_le_pow₀;exact Nat.one_le_cast.mpr L.property
lemma realize_volume (x:Letter B)(H':Hol G)(h:E ≥ e)(hv:d ≤ R)(hp:d<D)(hw:∀ i,d≤J i)(w:Wells τ F V H ρ a σ η δ Z Z W W E)(c:Payroll K B o (graded F Z) V E R D τ σ η μ)(hL:∀ i,2≤(F i).L.val)(hT:∀ i,Court o B (T i))(hq:∀ i,Qual (T i x) o E (σ i))
    (hS:∀ i,A i= avenue B ρ a (graded F Z i) (V i) (H i) (hL i) (W i) (T i))(hr:r≤ e+slots B x)(hU:∀ j m:ℕ,precede e r j m → Tender τ o σ (fun _=>1) (fun i p=> T i x p j m)) (he:∀ y j k,itinerary B x e r y j k → Tender τ o η (fun _=>1) (fun i p=> A i y p j k)): Nextpay o τ σ η μ (fun _=>1) r (fun i p=>T i x p e r) (fun i p=> A i x p e r):= by
    let R' (i:X):= migrates (D:=D) a (graded F Z i) (V i) K (W i) ρ (H i) (hL i) d d; let U i:= R' i (T i x)
    let k i:= pTrain B ρ a (graded F Z i) (V i) (H i) (hL i) (W i) (T i)
    let C (i:X)(x:Letter B):= heightK (F i).L d (Pose.weight B x)
    have H₁ i: Court o B (A i) ∧ larch (A i) (k i)=R' i∘ T i := by rw [hS]; exact axle _ _ _ _ _ _ _ _ _ (hT i) (w.aV i) w.pharmacy H' hp (hw i) (w.church i)
    have HC i: Colfax (Pose.slots B) (Pose.weight B) (k i) (C i) := performed _ _ _ _ _ _ _ _ _ _ H' hp (hw i) (w.church i) (w.aV i) w.pharmacy (hT i)
    have hh : r≤R+E:= by have := slotsFits B x;omega
    have h': Mill d r e (graded F Z) V K hL o τ η (fun _=>1) (fun i=> T i x) U:= mill_first w (fun _=>zero_le_one) hL _ _ e r h hU
    have hX j i (he:j<e∨ j=e∧ r ≤ Pose.slots B i): Soft τ (fun z=> coeff j (k z i x)):= (Fidelity c h' hU h hh (fun i=>(hT i).officers x) ((slotsFits B x).trans hv) hq (fun i=>rent_city x i hT e) (fun _=>zero_le_one) (by omega) j i he).pact (fun _=>le_rfl)
    have hD:Tender τ o η (fun _=>1) (fun i p=>Clover.track B (A i) (k i) x p e r):=(purchased (δ:=δ) x e r HC HC (fun i=> (H₁ i).1) (fun i=> (H₁ i).1) (fun i j h=> Pact.constant (hX j i h)) (fun y j k h=> Matched.constant (T:=_) (he y j k h))).1
    have hx:= ticker c h' hU h hh (fun i=>(hT i).officers x) ((slotsFits B x).trans hv) (fun i=>rent_city x i hT _) (fun _=>zero_le_one)
    apply nextsolve (b:= fun i=> C i x) (S:=fun i p=> U i p e r) hx hD _ (fun _=>crown_weight _ x)
    intro i p; unfold U; rw [show R' i (T i x)=larch (A i) (k i) x from (congr_fun (H₁ i).2 _).symm,employee,(HC i).due]
end YM.FormalBulk08.Clover
