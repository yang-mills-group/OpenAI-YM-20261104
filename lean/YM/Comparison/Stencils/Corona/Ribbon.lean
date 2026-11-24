import YM.Comparison.Stencils.Rotation
import YM.PertExtension.PacketFourier
/-!
# Positive-oriented face currency

Common translation and H ledgers. Sign is the recorded face orientation,
not a scalar-field mirror. Curl covariance below is NOT an IR
prescription: this file reads the full torus CURL symbol, with no inversion
image. On the cover use the actual Wilson one for the given G (at top;
not post-integration or kinetic reset).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Corona
open Lattice Exterior Function Filter Finset Matrix 
open Next PertExtension PertExtension.LatticePT PertExtension.LatticePT.Projection
open scoped BigOperators Topology ContDiff Classical
variable {R U E:Type*} [AddCommGroup R] [One R] [AddCommGroup E]
variable {G : Gauge} {s : Signed} {n : Side}

abbrev act (p : Face R) (A : Links R E): E:= linkSum A p.1 (square p.2.val.1 p.2.val.2)

lemma act_simple (x : Four R) (p:PlaqAxes) (A:Links R E): act (x,p) A=
    A (x,p.val.1)+A (x+step p.val.1,p.val.2)-A (x+step p.val.2,p.val.1)-A (x,p.val.2):=by
  unfold act square
  simp [linkSum,Step.used,Step.vec,negDir,posDir,sub_eq_add_neg,add_assoc,add_comm,add_left_comm]

/-- Pull on full link charts (no period/patch choice yet). -/
def tour (s:Signed) (z : Four R) (A:Links R E): Links R E:= fun e =>
  let v:= (posDir e.2).rotate s; let x:= affine s z e.1
  if v.neg then -A (v.used x) else A (v.used x)
lemma touring (s:Signed) (z:Cover)(A:Links ℤ G.Color) : tour s z A=pullLogs A s z:=rfl

set_option maxHeartbeats 1400000 in
lemma stroll [Module ℝ E] (s : Signed) (z : Four R) (I: Face R) (A:Links R E) : act I (tour s z A)=
    Free.turned s I.2 • act (Face.send s z I) A:=by
  obtain ⟨x,p⟩:=I
  have h (k:Axis) : s.act (step k:Four R)= if s.flip k then -step (s.perm k) else step (s.perm k) := by rw [← Step.vec_pos, ← Step.vec_rotate]; simp [Step.rotate,Step.vec,posDir]
  rcases lt_or_gt_of_ne (s.perm.injective.ne p.property.ne) with hm|hm <;>
    simp only [act_simple,Face.send,Free.turned,Face.lower,atFace,affine,Signed.act_add,h,tour,PlaqAxes.rotate,PlaqAxes.ordered,Step.rotate,posDir, Step.vec,Step.used, Bool.false_xor] <;>
    cases ha:s.flip p.val.1 <;> cases hb:s.flip p.val.2 <;>
    simp only [min_eq_right hm.le, min_eq_left hm.le,max_eq_left hm.le,max_eq_right hm.le,hm.not_gt,hm,if_true,if_false,Bool.false_eq_true,neg_one_mul,one_mul,neg_neg,neg_smul,one_smul] <;> abel_nf

lemma phi (n:Side) (s:Signed) (z:Cover) (a:Face ℤ) :
    (wrap n (Face.send s z a).1,(Face.send s z a).2)=Face.send s (wrap n z) (wrap n a.1,a.2):=by
  simp only [Face.send,Face.lower,atFace,map_add,affine];
  rw [show wrap n (s.act a.1)=s.act (wrap n a.1) from ?_];
  · split <;> split <;> simp only [map_zero,wrap_vec]
  funext i
  obtain ⟨i,rfl⟩:=s.perm.surjective i;
  change (((s.act a.1) (s.perm i) : ℤ) : Per n)=s.act (wrap n a.1) (s.perm i)
  rw [Signed.act_at, Signed.act_at]; split
  · push_cast; rfl
  rfl

-- real scalar plaquette response, no color. Disk theorem earliest accepted.
def price (p q:Face (Per n)):ℝ := (disk (shining q) p).re
lemma lives (q p:Face (Per n)) : price p q= act p (fun e=> (shining q e).re):=by
  unfold price disk Orb.Curl; rw [Complex.sub_re,Complex.sub_re,Complex.add_re]; exact (act_simple p.1 p.2 (fun e=>(shining q e).re)).symm
lemma projected (A : Links (Per n) ℝ) (q:Face (Per n)) :
    (∑ p:Face (Per n),price p q * act p A) = act q A:=by
  let B : Links (Per n) ℂ:=fun x=> A x
  have he (p:Face (Per n)) : disk B p= (↑(act p A : ℝ):ℂ):=by
     rcases p with ⟨x,p⟩; unfold disk Orb.Curl B; rw [act_simple]; push_cast; rfl
  have ht:= scalar_law B q; simp_rw [he] at ht
  have hh:= congr_arg Complex.re ht; rw [Complex.re_sum] at hh; simpa [price,Complex.mul_re] using hh
lemma exchanged (p q:Face (Per n)) : price p q=price q p:=by
  calc
    _ = ∑ r:Face (Per n),price r p*price r q:= by simp_rw [lives q]; rw [projected]
    _ = ∑ r:Face (Per n),price r q*price r p:=Finset.sum_congr rfl fun r _=>mul_comm ..
    _ = _:=by simp_rw [lives p]; rw [projected]
lemma squared (p q:Face (Per n)) : (∑ r:Face (Per n), price p r*price q r)=price p q:=by
  calc
     _ = ∑ r:Face (Per n), price r p*price r q:=Finset.sum_congr rfl fun r _=> congr_arg₂ (· * ·) (exchanged ..) (exchanged ..)
     _ = _:=by simp_rw [lives q]; rw [projected]
lemma reads_eq (s:Signed) (z:Site n) (A B:Links (Per n) ℝ) :
    (∑ p:Face (Per n),act p (tour s z A)*act p (tour s z B))=∑ p:Face (Per n),act p A*act p B:=by
  simp_rw [stroll,smul_eq_mul]
  let f:= Face.send s z; let u:=Equiv.ofBijective f (Finite.injective_iff_bijective.mp (Face.injective_send s z))
  refine Fintype.sum_equiv u _ _ ?_
  intro i
  change Free.turned s i.2 * act (f i) A * (_ * _) = _
  rw [mul_mul_mul_comm, Free.turned_sq,one_mul]; rfl

-- costate under motion. Use onto of pulled links, to test on whole range.
lemma tour_additive (A:Links R E) (p:Four R) (s:Signed) :
    let U : Links R (Multiplicative E):=fun i=>Multiplicative.ofAdd (A i)
    tour s p A = fun e=> Multiplicative.toAdd ((pull s p U) e):=by
  intro U; funext i
  simp only [tour,pull, Step.read]; split <;> rfl
lemma covers (s:Signed) (z:Four R) : Surjective (tour (E:=E) s z):=by
   intro A
   let y : Four R:= -(s⁻¹.act z)
   let C: Links R (Multiplicative E):=fun i=> Multiplicative.ofAdd (A i)
   let B:=pull s⁻¹ y C
   have he : pull s z B=C:=by rw [show B=pull s⁻¹ y C from rfl,pull_pull, inv_mul_cancel]; funext e; simp [y,affine,pull_one,Lattice.translate]
   refine ⟨(fun e=>Multiplicative.toAdd (B e)),?_⟩
   rw [tour_additive]; change (fun e=>Multiplicative.toAdd (pull s z B e)) = _; rw [he]; rfl

lemma procession (s:Signed) (z:Site n) (p q:Face (Per n)) :
    price p q=Free.turned s p.2*Free.turned s q.2*price (Face.send s z p) (Face.send s z q) := by
   let f:=Face.send s z
   let A:Links (Per n) ℝ:=fun e=>(shining (f q) e).re
   let W (p:Face (Per n)) : Links (Per n) ℝ:=fun e=>(shining p e).re
   obtain ⟨T,ht⟩:=covers (R:=Per n) s z (W p)
   have he : act p (tour s z A)=act (f q) T:=by
     rw [← projected (tour s z A) p]; simp_rw [lives p, ← show tour s z T= (fun e=>(shining p e).re) from ht]
     rw [reads_eq]
     calc
        _ = ∑ i:Face (Per n),price i (f q)*act i T:=Finset.sum_congr rfl fun i _=> by rw [lives]; exact mul_comm ..
        _ = _:=projected ..
   rw [stroll,← show price (f p) (f q)=act (Face.send s z p) A from lives ..,smul_eq_mul] at he
   calc
     _ = act q (tour s z T):=by rw [ht,exchanged p q,lives p]
     _ = _:=by rw [stroll,smul_eq_mul,← he]; ring
end YM.Comparison.Stencils.Corona
