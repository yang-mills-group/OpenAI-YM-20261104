import YM.RegulatorIR.Calibration.Polarity

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Epoch
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
variable {X V : Type}{W:X→Type}{A:(x:X)→Tariff (W x)}{L:Meter X}{F:X→ℝ≥0∞}{r s:ℕ}
variable {T U : (x:X)→Packet (W x) r} {P R:(x:X)→Layer (W x) (W x)}
namespace VacDay
lemma plain (h:Workday L A T): VacDay 1 L A T:=by obtain ⟨a,H,H₁⟩:=h;exact ⟨a,Carry.regular H,H₁⟩
lemma plain_r (h:VacDay 1 L A T): Workday L A T:=by obtain ⟨a,hp,H⟩:=h;exact ⟨a,hp.admit (Poly.oneQ L),H⟩
lemma limits_r (h:VacDay F L A T)(x:X)(hv:F x≠⊤): Limits (T x):=by obtain ⟨a,hp,H⟩:=h;exact bounds_from (H x) (hp.cost x hv)
lemma once (h:VacDay F L A T)(B:V→X): VacDay (F ∘ B) (L.us B) (fun i=>A (B i)) (fun x=>T (B x)):=by obtain ⟨a,h,H⟩:=h;exact ⟨_,h.us B,fun x=>H _⟩
lemma zero_r : VacDay F L A (fun _=>0 : (x:X)→Packet (W x) r):=⟨_,Carry.zeroQ F,fun _=> local_zero _⟩ -- unused x
lemma void_r {T:(x:X)→Packet (W x) 0} : VacDay F L A T:=⟨_,Carry.zeroQ F,fun _ i=> Fin.elim0 i⟩
lemma relax (h:VacDay F L A T){R:∀ i,Tariff (W i)}(hx:∀ i x y,(R i).road x y ≤ (A i).road x y):VacDay F L R T:=by
 obtain ⟨c,hc,H⟩:=h; refine ⟨c,hc,fun i j w=> le_trans ?_ (H i j w)⟩; apply quota_mono; intro p; exact Tariff.diameter_le _ (Tariff.diameter_unit ..) (fun j k=> (hx _ _ _).trans (Tariff.diameter_ge ..))
lemma add (h:VacDay F L A T)(hp:VacDay F L A U) : VacDay F L A (fun x=>T x+U x):=by obtain ⟨c,h,H⟩:=h;obtain ⟨a,hp,H'⟩:=hp; exact ⟨_,h.add hp,fun p=> local_add (H _) (H' _)⟩
lemma smulP (h:VacDay F L A T) {p:X→ℝ}(ht: Poly L fun x=> ‖p x‖ₑ): VacDay F L A (fun i=> p i • T i):=by obtain ⟨c,h,H⟩:=h;exact ⟨_,Carry.mul_left ht h,fun i=> local_gold (H i) _⟩
lemma rents (h:Workday L A T) {p:X→ℝ}(hp:Carry L F fun i=>‖p i‖ₑ): VacDay F L A (fun i=>p i • T i):=by obtain ⟨c,h,H⟩:=h; exact ⟨_,Carry.mul_right hp h,fun i=>local_gold (H i) _⟩
lemma tilts (h:VacDay F L A T) (c:ℝ): VacDay F L A (fun i=> c • T i):= h.smulP (p:=fun _=>c) (Poly.standard _ (by finiteness))
lemma sub (h:VacDay F L A T)(hh:VacDay F L A U): VacDay F L A (fun i=>T i- U i):=by simp_rw [sub_eq_add_neg]; simpa only [neg_one_smul] using h.add (hh.tilts (-1))
lemma sum {Z:Type} {p:Z→∀ i,Packet (W i) r}(S:Finset Z)(hp:∀ i∈S,VacDay F L A (p i)) : VacDay F L A (fun i=>∑ j∈ S,p j i):=by
 induction S using Finset.induction_on with
 | empty=> simp;exact zero_r
 | insert a s ha ih=> simp_rw [sum_insert ha]; exact (hp a (mem_insert_self ..)).add (ih (fun i hi=>hp i (mem_insert_of_mem hi)))
lemma sym (H:VacDay F L A T) : VacDay F L A (fun i=>Packet.symmetry (T i)):=by obtain ⟨c,hc,H⟩:=H; exact ⟨c,hc,fun i=> local_symmetry (H i)⟩
lemma rays (H:VacDay F L A T)(h:Beam L A P)(i:Fin r): VacDay F L A (fun x=>Packet.ray i (T x) (P x)):=by
 obtain ⟨c,hc,H⟩:=H;obtain ⟨p,hp,h⟩:=h; exact ⟨_,Carry.mul_right hc hp,fun x=> ray_local i _ (h x).1 (h x).2 (H x)⟩
lemma rays_t (H:Workday L A T)(h:RailDay F L A P)(i:Fin r): VacDay F L A (fun x=>Packet.ray i (T x) (P x)):=by obtain ⟨c,hc,H⟩:=H; obtain ⟨p,hp,h⟩:=h; exact ⟨_,Carry.mul_left hc hp,fun x=> ray_local i _ (h x).1 (h x).2 (H x)⟩
lemma pull_t (H:VacDay F L A T)(h:Beam L A P): VacDay F L A (fun i=> Packet.draft (P i) (T i)):=by obtain ⟨c,hc,H⟩:=H; obtain ⟨p,hp,h⟩:=h; exact ⟨_,Carry.mul_right hc (hp.powQ r),fun i=> local_draft (h i).1 (h i).2 (H i)⟩
lemma loop_p {T: (x:X)→ Packet (W x) (r+2)}(H:VacDay F L A T)(h:Beam L A P):VacDay F L A (fun i=> Packet.loop (T i) (P i)):=by obtain ⟨c,hc,H⟩:=H; obtain ⟨p,hp,h⟩:=h; exact ⟨_,Carry.mul_left hp hc,fun i=> Packet.loop_local (H _) (Layer.row_to_sup (h i).1)⟩
lemma loop_t {T:(x:X)→Packet (W x) (r+2)}(H:Workday L A T)(h:RailDay F L A P):VacDay F L A (fun i=> Packet.loop (T i) (P i)):=by obtain ⟨c,hc,H⟩:=H; obtain ⟨p,hp,h⟩:=h; exact ⟨_,Carry.mul_right hp hc,fun i=> Packet.loop_local (H _) (Layer.row_to_sup (h i).1)⟩
lemma splice_m {T:(x:X)→Packet (W x) (r+1)}{U:(x:X)→Packet (W x) (s+1)}(h:VacDay F L A T)(hv:Workday L A U): VacDay F L A (fun i=> Packet.splice (T i) (U i)):=by obtain ⟨c,h,H⟩:=h; obtain ⟨p,hp,hV⟩:=hv; exact ⟨_,h.mul_right hp,fun i=> Packet.splice_local _ _ (H i) (hV i)⟩
lemma splice_p {T:(x:X)→Packet (W x) (r+1)}{U:(x:X)→Packet (W x) (s+1)}(h:Workday L A T)(hv:VacDay F L A U): VacDay F L A (fun i=> Packet.splice (T i) (U i)):=by obtain ⟨c,h,H⟩:=h; obtain ⟨p,hp,hV⟩:=hv; exact ⟨_,Carry.mul_left h hp,fun i=> Packet.splice_local _ _ (H i) (hV i)⟩
end VacDay
end YM.RegulatorIR.Epoch
