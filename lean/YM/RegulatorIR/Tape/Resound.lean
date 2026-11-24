import YM.RegulatorIR.Tape.Senses

/-!
# Ward replacement genuine for every projected orbit at finite regulator
End-use of expansions in *cover* soft form. No claims on limiting λ until
alignment hypotheses supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Taping
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W:Type} {u b p j k s m i:ℕ}{M: W→ℕ}{n:Page M→Side} {L:Meter W}{D:Choice M}
variable {S:Heir n G} (R: Reel S)
section Orbit
variable {f c:Side}{P:ℝ}{A:Deck P (Foot G) (Book G f)}{B: Deck P (Foot G) (Book G c)}
variable (D: GridStep A B) {J₀: Layer (Foot G) (Foot G)}{V:Bride G}

lemma noble (C:Passport A B D J₀ V) {T:Orders (Book G f)}(h:∀ i ≤ p, Within (i+m) (T i)) (hs:∀ x y:ℝ→Horizon G f, ContDiffAt ℝ ∞ x 0 → ContDiffAt ℝ ∞ y 0 → reel_prop x y → Squares p (reel T m x) (reel T m y)) {e:ℕ}(he:e≤p) : (grain D J₀ V).WayO T e:=by
 let U:= grain D J₀ V
 change shot _ T e=shot _ T e; apply Gradient.consent U.tunnel U.run T (fun i=>i+m) T _ (fun i hi=>h i (hi.trans he)) (fun i hi=>h i (hi.trans he))
 intro v
 rw [chill, chill, port D J₀ V C, lift_eq]; simp_rw [← rhyme_tube]
 exact (hs _ _ (current_space _ _) contDiffAt_const (current_event _ (pair_even _ C.radians _)) _ he).symm
end Orbit
namespace Azur
variable {R}
variable {J: Flap M → Layer (Foot G) (Foot G)} {V:Flap M → Bride G}
variable {c: Flap M→ℝ≥0∞}
variable (C: Azur R J V k L c) (P: Inspires J V S)
include C P
-- no growth claim in STEAM
lemma pack (w:Flap M)(p:ℕ) :Steam (S.sight w).space p:=by intro i hi; obtain ⟨c,hc,H⟩:= C.bolts P i;exact ⟨_,hc.cost w,fun u=>(quota_mono _ fun j=> Premium.width_unit _ j).trans (H w u)⟩
lemma packL (w:Flap M)(p:ℕ): Steam (S.sight w).straight p:=by
 intro i hi; have ht:= C.prepaid w; rw [P.tune]; let A:=grain (S.frames w) (J w) (V w)
 refine ⟨c w,ne_top_of_le_ne_top ENNReal.one_ne_top (C.caps w),?_⟩; intro x; by_cases hg:i=0
 · subst i
   let W:Tuple (Foot G) 1≃Foot G:= Equiv.funUnique ..
   rw [quota_base,← W.symm.tsum_eq]
   have he(y) : A.straight x 0 (W.symm y)=J w x y:=rfl
   apply le_trans (le_of_eq (show _= quota (J w x) 1 from by rw [quota_base];exact tsum_congr fun y=> by rw [he y]))
   exact (quota_mono (J w x) (fun a=>(taskK k S w).unit _ _)).trans (ht x)
 rw [show A.straight x i=0 from funext fun a=> if_neg hg,quota_zero]; exact bot_le
variable (T:S.Accounts) (F:T.Report m)(U: W→ Portrait G)
variable (B: S.Supplies T L p k)(X : Halo.Aug.Amenities S L p k)(hk:14≤k)
variable (Y : R.Follows T)(hs:∀ w,BasisT m s (U w) (F.main (Page.opening M w)))
include hs hk X B Y
lemma preWard : ∀ w i,i ≤ p→ (S.sight w).Way (F.main w.prev) i:=by
 rintro ⟨w,n,h⟩ i he; let v:Flap M:=⟨w,n,h⟩;let Jv:= F.main v.prev; let A:=S.sight v
 have hx: Ranks m Jv:= F.cap_b (essential R) _
 have h' : Cluster.Bill Jv i := fun e hb r=> cusp_b R T F w B X Y C.run hs n h.le r _ (hb.trans he)
 refine consents A.straight A.space Jv hx ?_ (C.packL P v i) (C.pack P v i) h'
 intro s x e hv; let G:= grain (S.frames v) (J v) (V v); let t:= Cluster.Brief.tile s; let z:=dilute t x
 unfold A; rw [P.tune v,setup,stylist]; apply Eq.symm
 have hp:= C.invoke v
 exact Gain.plasma (basicB (J v) z) (basicP (V v) z) R w n h.le T F B X hk Y C.run hs (basic_cov _ _ _ hp.costL) (basic_cost _ _ _ hp.costH) (hv.trans he)
lemma ordWard : ∀ w i,i ≤ p → (S.sight w).WayO (T.change w.prev) i:=by
 rintro ⟨w,n,h⟩ i hi; let p':Flap M:=⟨w,n,h⟩; change (S.sight p').WayO (T.change p'.prev) i; rw [P.tune]
 refine noble _ (C.invoke _) (m:=2) ?_ ?_ hi
 · intro i _ j he
   have hh := T.cap_b (essential R) p'.prev; have hK:= T.cap_o (essential R) p'.prev
   by_contra! hv; apply he; unfold Sky.Accounts.change;rw [show T.orb _ i j=0 from Classical.not_not.mp (fun hg=>(not_le.mpr hv) (hK _ _ hg).2),show T.bulk _ i j=0 from Classical.not_not.mp (fun hg=>(not_le.mpr hv) (hh _ _ hg).2), Deck.desk_zero,sub_self]
 intro x y Hx Hy hh;exact corsage R T B X hk Y C.run w n h F hs Hx Hy hh
lemma explicitO : ∀ w i,i ≤ p→ (S.sight w).WayO (F.deviation w.prev) i:=by
 rintro ⟨w,n,h⟩ i hi; let p':Flap M:=⟨w,n,h⟩; change (S.sight p').WayO _ _; rw [P.tune]
 refine noble _ (C.invoke _) (m:=m) ?_ ?_ hi
 · intro i _ j he; have hh:= F.cap_b (essential R) p'.prev i; have hK:= F.cap_o (essential R) p'.prev i
   by_contra! hv;apply he; unfold Sky.Accounts.Report.deviation; rw [show F.point _ i j=0 from Classical.not_not.mp (fun hg=>(not_le.mpr hv) (hK j hg)),show F.main _ i j=0 from Classical.not_not.mp (fun hg=>(not_le.mpr hv) (hh j hg)), Deck.scroll_zero,sub_self]
 intro x y Hx Hy hh; exact Halo.grazed R T F w B X hk Y C.run hs n h.le Hx Hy hh
end Azur
end YM.RegulatorIR.Taping
