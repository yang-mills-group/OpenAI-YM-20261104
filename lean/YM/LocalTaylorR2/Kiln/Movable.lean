import YM.LocalTaylorR2.Kiln.Floret

/-! # Charge across actual moving field. Uses only the hot aperture published for the Atom. "Cursor" cut is on true field length. Does not take a new footprint dilation in this step. Follows Canvas preserver. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Kiln
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Work.G05
variable {G:Gauge}{c f L n : Side} {S:StepData c f}{P:Teller G}{T:Tube G S}{F:Forest S.ratio}
variable {d j k p:ℕ}{s:ℝ}{R:Rep G f}
variable {X X': Coat T F} {A : ℕ→ Atom G d}{i:Trans f}
variable {E :Type}[NormedAddCommGroup E][NormedSpace ℝ E] {y:E}
-- Same functions when interpreted in coarse root gauge via actual along Support.atoms
lemma moss (t:Site f→G.El) (U:Config G f)(A: Atom G d)(i: Site f) (b:Signed)(h:A.Invariant): A.unmasked (pull b 0 (gauge t U)) i = A.unmasked (pull b 0 U) i:=by
  rw [Work.F05.pull_gauge_zero]
  unfold Atom.unmasked; simp_rw [Work.F05.slot_gauge]; exact h _ _
private lemma pens (i : Bond f) (Y : Support c)(h:X.Hot i)(he:atEdge S i∈Y): i ∈ X.plaza Y:= mem_filter.mpr ⟨mem_univ _,h,Finset.not_disjoint_iff.mpr ⟨_,he, center_end i⟩ ⟩

lemma warranted (a s v b:ℝ)(J:Basecamp G)
    (V:E→ Config G c)(u:E→Directions G f)(w:E→ Air f G)(i:Trans f)(j:ℕ){β:ℝ}{z : Air f G}
    (hh: Mode V y j v) (ht:Clutch X z a β s y j V u w)(hA:Room P S T X.x)
    (hk :(A i.2.2).Invariant)(h: light X A i)(hp:¬ dim X i)(hd: ¬ (fun t=> pane X a A i (u t))=ᶠ[𝓝 y] fun _ =>0)
    (he: Brush j b 1 (fun t=> point J X.χ (bed X) (axis S i) (V t)) y)
    (hx:∀ᶠ k in 𝓝 y, AgreeNear id (axis S i) (bed X) (pedestal (axis S i) (V k)) (increment 1 (point J X.χ (bed X) (axis S i) (V k)))) :
    let ℓ x:= argument J (vary X (V x)) A i (u x)
    let g:= royalty G; let r:= 4*(X.B:ℝ)*(v*g); let D := g*((s+4*a*X.t)*g)*(1+(r+1+r))^j
    Brush j (b + |D| + (b + |D|)) 1 ℓ y ∧ ∀ᶠ t in 𝓝 y, (A i.2.2).unmasked (pull i.1 0 (X.input (worldZ X β z))) i.2.1= latent A S i (ℓ t):= by
  intro ℓ g r D
  let o:= axis S i; let W t:= vary X (V t); let T' x t:= carrier o (V t) x
  have hF : 100 ≤ X.B := hA.sight.1
  obtain ⟨hB,hG⟩:= ht.darling _ hd
  let U:= X.input (worldZ X β z); let u' (t:E) (j':Bond f): Prop:=U j'= increment (replica S.ratio (V t)) ((W t).signal (u t)) j'
  have hv i (hi:distAt S i o ≤ bed X) (hh:i∉F.trunks): X.Hot i := far_active X.seeds F i (clear (v:=200*X.B) hp (by unfold dim at hp; unfold distAt bed at hi; unfold o at hi; omega)) hh
  constructor
  · have hr t (h: separation o t≤ X.B) : Brush j g r (fun y=> G.mat (T' t y)) y:=by
      apply (tour (carriage o t) o hh.pos hh.atLink).climb le_rfl
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (SliceRows.mileage o t).trans (Nat.mul_le_mul_left 4 h)) (mul_nonneg hh.pos (zero_le_one.trans (royalty_ge _)))
    apply Brush.pair (he.climb (le_add_of_nonneg_right (abs_nonneg D)) le_rfl)
    have hS := he.nonneg; apply Brush.fold zero_le_one (by positivity)
    intro j'; by_cases hb : atEdge S j' ∈ homeFoot X A i ∧ distAt S j' o ≤ bed X
    · by_cases hm:j'∈ F.trunks
      · apply Brush.zi _ (by positivity) zero_le_one; refine Eventually.of_forall (fun t=> ?_)
        change (ℓ t).snd j'=0; rw [show (ℓ t).snd j'= spinRow S _ ((W t).signal (u t)) j' from if_pos hb,spinRow,(W t).on_trunk _ _ hm, map_zero]
      have hj:= hv j' hb.2 hm
      apply (((decorate (g:=T' (atEdge S j')) (hr _ (hb.2.trans (by unfold bed; omega))) (hB j' (pens j' _ hj hb.1))).trim).climb ((le_abs_self _).trans (le_add_of_nonneg_left hS)) le_rfl).shimmy
      refine Eventually.of_forall fun x=> ?_; change (ℓ x).snd j'=_; rw [show (ℓ x).snd j' = spinRow S _ ((W x).signal (u x)) j' from if_pos hb,spinRow,(W x).at_hot _ _ hj]; rfl
    exact Brush.zi (Eventually.of_forall (fun t=> if_neg hb)) (by positivity) zero_le_one
  filter_upwards [hx,hG] with t ht hG
  let X':= increment (1:Config G c) (ℓ t).1
  rw [← moss (constantGauge (fun k=> T' k t) S.ratio) U (A i.2.2) i.2.1 i.1 hk]; apply spotlight
  intro q hq hhq
  have hf:= cursor hq hhq hA h
  rcases hf with ⟨h₁,h₂⟩; let e := Channel.edge i.1 q
  have hx: u' t e:=by
    by_cases H:e∈F.trunks
    · unfold u' U; rw [X.sliced _ _ H,increment,(W t).on_trunk _ _ H,G.mat_lieExp_zero,one_mul]; exact
        (if_pos (F.trunk_internal (by simpa using H))).symm
    change _ ∈ homeFoot X A i at h₁
    have hh':= hv e h₂ H
    change X.input ..= _; rw [← hG e (pens e _ hh' h₁),(W t).viewing (u t) _ hh']; unfold increment; rw [(W t).at_hot _ _ hh']; rfl
  have hℓ : (ℓ t).2 e= spinRow S (fun i=> T' i t) ((W t).signal (u t)) e:= if_pos ⟨h₁,h₂⟩
  have hz : replica S.ratio (gauge (fun x=> T' x t) (V t)) e= replica S.ratio X' e:= replica_near ht e h₂
  have he: gauge (constantGauge (fun x=>T' x t) S.ratio) U e = shaft S (ℓ t) e := by
    rw [show gauge (constantGauge (fun x=>T' x t) S.ratio) U e=gauge (constantGauge (fun x=>T' x t) S.ratio) (increment (replica S.ratio (V t)) ((W t).signal (u t))) e from (by unfold Lattice.gauge; unfold u' at hx; rw [hx]), ← tilt (S:=S)]
    unfold shaft increment; rw [hz,hℓ]; rfl
  rw [charge,charge,show _ = _ from he]
end YM.LocalTaylorR2.Kiln
