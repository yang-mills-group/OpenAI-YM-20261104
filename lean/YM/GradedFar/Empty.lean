import YM.GradedFar.Mask
import YM.GradedFar.Cancel

/-! Optional use of the assertions with **empty** Near. This is the
FVA2 empty-input convention of the same alphabet (no auxiliary point sent to
infinity). If replacing the empty tuple, the resulting price is really on the
field 1. -/
namespace YM.FVA2.GradedFar.Subarray
noncomputable section
open Set Filter Function Real PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {m : ℕ} {d : Fin 0 → ℕ} {N : WilsonPrescription G} {simple : G.Simple}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)

-- true sequence of C on empty input in graded & fixed cap bases
def unitC (_x : Points 0) (q : Q G) : PowerSeries ℂ :=
  if heft q = 0 then C (paygrade q.item (leaf G q.h)) else 0

private lemma scan_bill {n ℓ : ℕ} (u : Scan G n) (v : Scan G m) (hx : Guarded u ℓ) (hy : Guarded v ℓ) :
    Guarded (Fin.append u v) ℓ := by
  intro i; induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; exact hx i
  | right j => rw [Fin.append_right]; exact hy j

lemma spelled_party {n ℓ : ℕ} (V : Scale.Arenas G) (r : Regular V) (u : Scan G n) (v : Scan G m)
    {x : Points n} {y : Points m} (hd : Guarded u ℓ) (he : Guarded v ℓ) (hg : forest x y ∈ conf (n+m)) (j : ℕ) :
    coeff j (party (install V) x y u v) = V ℓ _ ⟨forest x y,hg⟩ j (Fin.append (tape u hd) (tape v he)) := by
  rw [party,caring (d:=ℓ) _ (scan_bill u v hd he) r hg]
  unfold O.Score.test Reg.Point.story; rw [coeff_mk]
  apply congrArg _
  funext i
  induction i using Fin.addCases <;> (unfold tape; simp only [Fin.append_left, Fin.append_right])

lemma read_lamp (h : ℕ) (y : Points m) (v : Scan G m) (x : Points 0) :
    Lamp (ordinary N) h y v (unitC x) = Lamp (ordinary N) 0 y v (unitC x) := by
  induction h with
  | zero => rfl
  | succ i ih =>
    rw [O.Bind.Lamp_step,ih]; unfold O.Bind.wage Settle
    simp [unitC, heft]

private lemma freeze_basis {ℓ d : ℕ} (B : Point G d (1+m)) (u : Sec G ℓ) (v : Tags G d m) (hd : ℓ ≤ d) :
    B (Fin.append (fun _ : Fin 1 => up hd u) v) =
      ∑ a : Toon G ℓ, coord a u *
        B (Fin.append (fun _ : Fin 1 => up hd (theory a)) v) := by
  have h := expand_near (d:=fun _ => ℓ) B (fun _ => u) v (fun _ => hd)
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Toon G ℓ)).symm] at h
  unfold combo at h
  simp only [Fin.prod_univ_one] at h
  exact h

lemma money_leaf {V : Scale.Arenas G} (r : Regular V) (v : Scan G m)
    {x : Points 0} {y : Points m} (hy : y ∈ O.Enh.Outside m) (j : ℕ) :
    coeff j (Lamp (install V) 0 y v (unitC x)) =
      V (totalG v) _ ⟨outgoing y,hy⟩ j (Fin.append
        (fun _ => leaf G (totalG v)) (tape v (guardT v))) := by
  rw [← LampT, map_sum]
  let F := V (totalG v) _ ⟨outgoing y,hy⟩ j
  change _ = F (Fin.append _ _)
  rw [show (fun _ : Fin 1 => leaf G (totalG v)) =
      (fun _ => up (Nat.zero_le (totalG v)) (leaf G 0)) from rfl,
    freeze_basis F (leaf G 0) (tape v (guardT v)) (Nat.zero_le (totalG v))]
  refine Finset.sum_congr rfl fun b _ => ?_
  change coeff j (unitC x (flash b) * lonelyG _ y (flash b) v) = _
  rcases b with ⟨k,b⟩
  obtain rfl : k = 0 := @Subsingleton.elim (Fin 1) _ _ _
  unfold unitC
  let q : Toon G 0 := ⟨0,b⟩
  rw [if_pos (show heft (flash (B:=Press.portDeck G) (⟨0,b⟩ : Toon G 0))=0 from rfl), coeff_C_mul]
  rw [lonelyG, spelled_party V r (ℓ:=totalG v) _ _ (by intro i; exact Nat.zero_le _) (guardT v) hy]
  rfl

private lemma missing_sep (x : Points 0) {y : Points m} (hy : y ∈ O.Enh.Outside m) :
    forest x y ∈ conf (0+m) := forest_sep (fun i => i.elim0) (O.Enh.room hy) (fun i => i.elim0)
include H
lemma read_empty (x : Points 0) (u : Scan G 0) (y : Points m) (v : Scan G m) (hy : y ∈ O.Enh.Outside m) (h : ℕ) :
    Basket (ordinary N) u v (unitC x) h x y = 0 := by
  unfold Basket; rw [read_lamp]
  apply sub_eq_zero.mpr
  ext j
  have hu := (H.separatedOPE (Teller.logNu 1)).wilson.dimensions
  rw [money_leaf hu v hy j]
  let w := tape v (guardT v)
  rw [spelled_party _ hu u v (ℓ:=totalG v) (fun i => i.elim0) (guardT v) (missing_sep x hy) j]
  let a := (⟨forest x y,missing_sep x hy⟩ : Scale.Stage (0+m))
  let b := (⟨outgoing y,hy⟩ : Scale.Stage (1+m))
  let p := fun _ : Fin 1 => leaf G (totalG v)
  change book N _ _ a j (Fin.append _ w) = book N _ _ b j (Fin.append p w)
  let z : Fin 0 ↪ Fin 1 := { toFun := fun i => i.elim0, inj' := fun i => i.elim0 }
  let m0 := Function.Embedding.refl (Fin m)
  have hp (i) (hi : i ∉ range z) : p i = leaf G _ := rfl
  have hu (i) (hi : i ∉ range m0) : w i = leaf G _ := False.elim (hi ⟨i,rfl⟩)
  rw [book_unit H (joint z m0) _ b (Fin.append p w) (lonely z m0 p w (leaf G _) hp hu)]
  congr 1
  · refine congrArg (fun a => book N _ _ a j) ?_
    apply Subtype.ext
    change forest x y=config (joint z m0) (forest _ _)
    rw [subforest,show x=config z (0:Points 1)
      from Subsingleton.elim ..]
    rfl
  rw [join]
  exact congrArg (fun p => Fin.append p w) (Subsingleton.elim ..)


lemma empty_unit (u : Scan G 0) : FarCoefficients (book N) u = unitC := by
  apply (H.separatedOPE (Teller.logNu 1)).wilson.uniqueF
  refine ⟨fun i h => False.elim (h (fun k => k.elim0)), fun i k => continuousOn_const,?_⟩
  intro S hs ht j d m K v hK hv k hk
  have h (i : ↥S × ↥K) (s : ℝ) : coeff k (Basket (ordinary N) u v
      (unitC i.1.val) j i.1.val (squeeze (-s) i.2.val)) = 0 := by
    rw [read_empty H _ u _ v (O.Enh.lives _ (hv i.2.property)) _, map_zero]
  simp_rw [h]
  exact Rain.nil _
lemma empty_component (x : Points 0) (u : Inputs G d) (q : Q G) :
    seriesComponent N x u q = unitC x q := by
  unfold seriesComponent
  simp_rw [empty_unit H, combo, Fin.prod_univ_zero]
  simp
lemma leaf_earn (x : Points 0) (u : Inputs G d) (p : ℕ) (t : ℝ) (q : Q G) :
    crop p t (seriesComponent N x u q) = if heft q=0 then paygrade q.item (leaf G q.h) else 0 := by
  rw [empty_component H x u q,unitC]
  split_ifs
  · simp only [crop_eq]; rw [Finset.sum_eq_single 0]; · rw [coeff_C, if_pos rfl,pow_zero,one_mul]
    · intro j _ h; rw [coeff_C,if_neg h,mul_zero]
    simp
  exact crop_zero p t

theorem empty_c (x : Points 0) (u : Inputs G d) (h p : ℕ) (t : ℝ) : cActual N x u h p t = leaf G h := by
  rw [← reconstructed (cActual N x u h p t)]
  simp_rw [coord_actual,leaf_earn H]
  rw [Fintype.sum_sigma, Finset.sum_eq_single (0:Fin (h+1))]
  · let φ := up (G:=G) (Nat.zero_le h)
    have Q := congrArg (fun v => φ v) (whole_grade (leaf G 0) (Scale.Level.leaf_0))
    simp only [map_sum,_root_.map_smul] at Q
    change ∑ a : Grade G 0, (if (0:ℕ)=0 then _ else 0) • theory _ = φ (leaf G 0)
    simp_rw [if_true]
    exact Q
  · intro k _ hk; refine Finset.sum_eq_zero fun b _ => ?_
    change (if k.val=0 then _ else (0:ℂ)) • _ = _
    rw [if_neg (show k.val ≠ 0 from fun h => hk (Fin.ext h)),zero_smul]
  simp

end
end YM.FVA2.GradedFar.Subarray
