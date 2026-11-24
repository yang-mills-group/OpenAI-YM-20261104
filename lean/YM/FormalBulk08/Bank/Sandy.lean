import YM.FormalBulk08.Bank.Dam

/-! Hull shift on ALL letters and covariance padded. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Matrix Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (L : Lodge P.patch) (h : P.patch.Branches K G)

def rayshot := dye (gamma G K P L h) (0:Row _ (Loc G 1)) (0:Row (Loc G 1) _) (0:Row (Loc G 1) (Loc G 1))
lemma ray_forms (n : Side) (x y) : (rayshot P L h).acts n (saddleP G (primary P.patch K n) L x) (saddleP G (primary P.patch K n) L y)= aqua (ferry P h L n).saddle x y := by
   unfold saddleP rayshot;rw [Equiv.trans_apply,Equiv.trans_apply,dye_spot,deadActs,deadActs,deadActs]; cases x <;> cases y <;> rfl
lemma ray_flip (n : Side) (x y) : (rayshot P L h).acts n x y=(rayshot P L h).acts n y x:= by
   let E:=saddleP G (primary P.patch K n) L;obtain ⟨x,hx⟩:= E.surjective x; obtain ⟨y,hy⟩:= E.surjective y
   rw [←hx,←hy]; unfold E; rw [ray_forms,ray_forms]; exact aqua_symm ..
lemma rayStrip {σ C : ℝ} (hx : 0≤C) (H : (gamma G K P L h).strip σ C) : (rayshot P L h).strip σ C:= fileStrip H (stillborn hx) (stillborn hx) (stillborn hx)
lemma ray_grated {σ B : ℝ} (hs : 0≤σ) (hb : 0≤B) (H : (gamma G K P L h).strip σ B) (n : Side) :
    Grate (lake n _) σ ((rayshot P L h).acts n) ((Fintype.card (BoardL G P.patch L))*B):= by
   have he:=trundle n (rayshot P L h) (rayStrip P L h hb H) hb hs
   refine ⟨he.costs,fun x=>?_⟩; have ht:= he.rows x; simp_rw [rinkshine,skit_sub n _ x.1] at ht; exact ht
lemma ray_cover {σ B : ℝ} (hs : 0≤σ) (hb : 0≤B) (H : (gamma G K P L h).strip σ B) :
    Grate (fame _) σ (lands (rayshot P L h)) ((Fintype.card (BoardL G P.patch L))*B) ∧
    ∀ x y, lands (rayshot P L h) x y=lands (rayshot P L h) y x := by
   have ht:=rayStrip P L h hb H; have he:=grad_line (rayshot P L h) ht hb; have hh:=landing_row _ (Row.rights _ _ ht hs);refine ⟨⟨he.costs,fun x=>?_⟩,fun x y=>tendsto_nhds_unique (hh x y) ((hh y x).congr' (.of_forall fun n=> ray_flip P L h n _ _))⟩
   have hx:=he.rows x; simp_rw [linkshine,← show ∀ (y:Biglot _), (fame _).d y x=size (y.1-x.1) from (fun _=>rfl), Reach.turn _ _ x] at hx;exact hx

variable (K)
def zealand (G : Gauge) := dye (unitRow _) (locating G K P L) (0 : Row (Loc G 1) (Minor G P.patch L)) (unitRow _)
lemma zealandPay {σ C : ℝ} (h : (locating G K P L).strip σ C): (zealand K P L G).strip σ (max 1 C):=fileStrip (strip_mono Work.F08.strip_unit le_rfl (le_max_left ..)) (strip_mono h le_rfl (le_max_right ..)) (stillborn (zero_le_one.trans (le_max_left ..))) (strip_mono Work.F08.strip_unit le_rfl (le_max_left ..))
variable {K}
abbrev outshift (G : Gauge) (K : KernelChoices) (n : Side) := Matrix.fromBlocks (1:Matrix (Pine G _ (Reef.floor K P L n)) (Pine G _ (Reef.floor K P L n)) ℝ) (pMean G K P n (Reef.floor K P L n)) 0 (1:Matrix (wire G n) (wire G n) ℝ)
lemma twig (n : Side) (σ A : ℝ) (hs : 0<σ) (ha : 0≤A) (h : (Flight.duo K.penalty P).A0.strip σ A) (x y) :
   (zealand K P L G).acts n (saddleP G (primary P.patch K n) L x) (saddleP G (primary P.patch K n) L y)= outshift P L G K n x y := by
   obtain ⟨C,hC,H⟩:=Lodge.bothPay G K L σ hs
   have he : (locating G K P L).acts n=repackM (L.splitting (S:=primary P.patch K n)) (Equiv.refl _) (pMean G K P n (Reef.floor K P L n)):= ((H _ A ha h).2.2 n).1
   unfold saddleP zealand;rw [Equiv.trans_apply,Equiv.trans_apply,dye_spot,acts_unit,acts_unit,deadActs,he]
   cases x <;> cases y <;> first|rfl|simp [Matrix.one_apply,outshift,repackM]
lemma sash_lever {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] (H : Hull V I) (u : Pap (V⊕I)) (D : Matrix V I ℝ) (he : H.drift=draught D) : lever H u= PowerSeries.map (mixRows (Matrix.fromBlocks (1 : Matrix V V ℝ) D 0 (1:Matrix I I ℝ))).toRingHom u:= by
   unfold lever; rw [show MvPolynomial.aeval _ = mixRows _ from ?_]
   ext x; cases x <;> simp [he, draught,mixRows, Fintype.sum_sum_type, Matrix.one_apply,ite_mul,apply_ite MvPolynomial.C]
lemma tilt_hull (n : Side) (u : Pap (Pine G (primary P.patch K n) (Reef.floor K P L n)⊕ wire G n)) :
   lever (ferry P h L n) u= PowerSeries.map (mixRows (outshift P L G K n)).toRingHom u := by
   exact sash_lever _ _ (pMean G K P n (Reef.floor K P L n)) rfl
lemma shifted (n : Side) (u : Pap (Pine G (primary P.patch K n) (Reef.floor K P L n)⊕ wire G n)) (σ A : ℝ) (hs : 0<σ) (ha : 0≤A) (hx : (Flight.duo K.penalty P).A0.strip σ A) :
    joust (saddleP G (primary P.patch K n) L) (lever (ferry P h L n) u)=PowerSeries.map (mixRows ((zealand K P L G).acts n)).toRingHom (joust (saddleP G (primary P.patch K n) L) u) := by
   rw [tilt_hull]; apply mix_pane; exact twig P L n σ A hs ha hx
end YM.FormalBulk08.Bank
