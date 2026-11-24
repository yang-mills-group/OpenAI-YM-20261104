import YM.OPE.Compatible.Roan.Hope
/-! # temperate dependence of refunds on footprints and costumes. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Score Lav
variable {G:Gauge} {X:Type}
section Inv
variable {Z:Zone X}
abbrev Tunable (Z:Zone X)(A:X→price):Prop:=∀ i, Z.Invoice (fun x=>A x i)
variable {A B t:X→price}
lemma Tunable.fuse (h:Tunable Z A)(he:Tunable Z B): Tunable Z (fun x=> JumpP (A x) (B x)):=fun _=> (h _).mul (he _)
lemma Tunable.hike (h:Tunable Z A)(i:ℕ): Tunable Z (fun x=>hikeP (A x) i):=by
        induction i with
        | zero=> exact fun _=> Zone.Invoice.const _
        | succ i ih=> exact h.fuse ih
lemma Tunable.reel (h:Tunable Z A)(he:Tunable Z B)(i:ℕ):Tunable Z (fun x=>reelP (A x) (B x) i):=by
        induction i with
        | zero=> exact fun _=> Zone.Invoice.const _
        | succ i ih=> exact fun j=> (he.fuse (h.hike i) j).add (h.fuse ih j)
lemma clamp_I {f g:X→ℝ}(h:Z.Invoice f)(he:Z.Invoice g): Z.Invoice (fun i=> max (f i) (g i)):= by
        refine (h.norm.add he.norm).weaken ?_; intro i;  change ‖max _ _‖≤ ‖‖f i‖+‖g i‖‖; rw [Real.norm_eq_abs (‖_‖+‖_‖),abs_of_nonneg (by positivity)]; rcases le_total (f i) (g i) with hp|hp; · rw [max_eq_right hp]; linarith [norm_nonneg (f i)]
        rw[max_eq_left hp]; linarith [norm_nonneg (g i)]
lemma Bzt_I {U C D:X→price}(h:Tunable Z U)(he:Tunable Z A)(ht:Tunable Z B)(ha:Tunable Z C)(hp:Tunable Z D): Z.Invoice (fun x=> telemetry.Bezel (U x) (A x) (B x) (C x) (D x)):= by
       exact ((((h 2).mul ((ha.fuse ht 2).add (he.fuse hp 2))).add ((he 1).mul ((h 2).mul (hp 2)))).add (((h 2).mul (ha 2)).mul (ht 1)))
lemma Glz_I {U:X→price}(h:Tunable Z U)(he:Tunable Z A)(ht:Tunable Z B): Z.Invoice (fun x=> telemetry.Garlic (U x) (A x) (B x)):=(((h.fuse he 2).mul (ht 2)).add (((h 2).mul (ht 2)).mul (he 1))).add ((h 1).mul ((he 2).mul (ht 2)))
lemma Alc_I {U C:X→price}{B:ℕ→X→price}(h:Tunable Z U)(he:Tunable Z C)(hp:∀ n,Tunable Z (B n))(m n:ℕ): Z.Invoice (fun x=> Alc m n (U x) (C x) (fun i=>B i x)):= clamp_I (Bzt_I h (he.hike _) (he.hike _) (he.reel (hp _) _) (he.reel (hp _) _)) (Glz_I h (he.hike _) (he.reel (hp _) _))
lemma Duo_I {t s:X→ℝ}(h:Z.Invoice t)(he:Z.Invoice s): Z.Invoice (fun i=>Duo (t i) (s i)):= ((Zone.Invoice.const (2:ℝ)).mul h).mul he
lemma Tri_I {t s u:X→ℝ}(h:Z.Invoice t)(he:Z.Invoice s)(hu:Z.Invoice u): Z.Invoice (fun i=>trioK (t i) (s i) (u i)):=by
       unfold trioK; exact (((Zone.Invoice.const (6:ℝ)).mul h).mul he).mul hu
lemma Alps_I {U C:X→price}{P:ℕ→X→price}(n m:ℕ)(h:Tunable Z U)(hA:Tunable Z A)(hC:Tunable Z C)(ht:Tunable Z t)(hP:∀ i,Tunable Z (P i)): Z.Invoice (fun x=> Alps3 m n (U x) (A x) (C x) (t x) (fun i=> P i x)):= clamp_I (clamp_I ((Zone.Invoice.const (2:ℝ)).mul (Tri_I (h 4) (hC.hike m 4) (hC.hike n 4))) (((Tri_I (hA 4) (hC.hike m 4) (hC.hike n 4)).add (Tri_I (hC.reel ht m 4) (h 4) (hC.hike n 4))).add (Tri_I (hC.reel ht n 4) (h 4) (hC.hike m 4)))) ((Zone.Invoice.const (2:ℝ)).mul (clamp_I (Alc_I h hC hP m n) (Alc_I h hC hP n m)))
lemma Jive_I {U C:X→price}(h:Tunable Z U)(hA:Tunable Z A)(hC:Tunable Z C)(ht:Tunable Z t)(hS:Tunable Z B)(n:ℕ): Z.Invoice (fun x=> Jive n (U x) (A x) (C x) (t x) (B x)):= clamp_I (clamp_I ((Zone.Invoice.const (2:ℝ)).mul (Duo_I (h 2) (hC.hike n 2))) ((Duo_I (hA 2) (hC.hike n 2)).add (Duo_I (hC.reel ht n 2) (h 2)))) ((Zone.Invoice.const (2:ℝ)).mul ((h 2).mul (hC.reel hS n 2)))
end Inv
end YM.OPE.Borealis.Galea
