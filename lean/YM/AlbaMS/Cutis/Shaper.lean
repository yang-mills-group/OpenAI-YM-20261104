import YM.AlbaMS.Cutis.Form

/-!
# Rank transport of common Book, not assuming horizon fits

Physical a factors. prolong to torus & compressed orbit. Segment Ze contact
kinetic for orthonormal indices not normalized per-volume (these are totalized
full actions including multiplicities chosen in Accord).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter LinearMap
open scoped BigOperators Classical Topology Matrix
open Bric Coil Loft Inlay Inlay.Net
variable {E B I J R S : Type*}[Fintype E][Fintype B][Fintype I][Fintype J][CommRing R][Algebra ℚ R]
variable {G:Gauge}{Ω:Net E B}{H:Net I J}(F:Odom.Book Ω G)(P:Tune R){r a:ℝ}
abbrev phys (a:ℝ):= (waveLots F).scale (a^2) (a^3)
lemma museum (h:0<a): F.first a h=(phys F a).combo:=by
  have hh (i:Leaf G E B): weft (Tune.baseT a h).loomT (varC ℝ ø i)=((Tune.baseT a h).loomT i) • varC ℝ ø i:=by ext l; by_cases h:l=[i] <;> simp [wefts,var_read,h]
  let α := Tune.baseT a h; let P:=waveLots F; let U:=weft (ρ:=@ø (Flit G E) (Flit G B)) α.loomT
  have hu (i j : Flit G E): U (A (B:=Flit G B) ℝ i*A ℝ j)=a^2 •(A ℝ i*A ℝ j):=by unfold U; rw [weft_mul, hh (Place.a i), hh (Place.a j), smul_mul_assoc,mul_smul_comm, smul_smul]; simp [Tune.baseT,Tune.loomT,Place.a,pow_two]
  have he (i:Flit G E)(j:Flit G B): U (K (B:=Flit G B) ℝ i*C ℝ j)= a^3 • (K ℝ i * C ℝ j):=by unfold U; rw [weft_mul,hh (Place.k i),hh (Place.c j), smul_mul_assoc,mul_smul_comm,smul_smul]; congr 1; change α.loomT _ * α.loomT _=a^3; simp [α,Tune.loomT,Tune.baseT,Place.k,Place.c,pow_succ]
  unfold Odom.Book.first Tune.kinetic; rw [bodyN,phys,P.markScale];
  change U P.combo = _; unfold Lot.combo Lot.boson Lot.tong; rw [map_add]; simp_rw [map_smul,map_sum,map_smul, he, hu, Finset.smul_sum, smul_comm (a^_)]; -- maybe loop
lemma plaza : F.fair P=((phys F P.a).beam P.D).combo:=by rw [Lot.beacon,← museum F P.ha];rfl

variable (u:Net.Receipt G Ω H){X : Odom.Book H G}
abbrev Φ := Matrix.of u.φ
abbrev Ψ := Matrix.of u.ε
lemma bookN (X : Odom.Book H G) (h: F.Unify X u r) : (waveLots X).combo=r • u.track (waveLots F).combo:=by
  rw [← bodyN,← bodyN,h.file, map_smul]; congr 1; exact (shot_rank 2).symm
omit [Fintype I][Fintype J] in
private lemma dripper (i:Leaf G I J)(f:Heave G E B ℝ): D i (u.track f)= u.track (drip Finset.univ u.skein i f):= shot_D ..
omit [Fintype I][Fintype J] in
lemma mantle (f : Heave G E B ℝ)(x y:Leaf G I J): u.track f [x,y]= ∑ i:Leaf G E B, ∑ j:Leaf G E B,u.skein i x*u.skein j y*f [i,j]:=by
  change D y (D x (u.track f)) []=_; rw [dripper,dripper]; change drip _ _ _ _ [] =_; rw [drip_apply (x:=x), map_sum,sum_read]; refine Finset.sum_congr rfl (fun i _=>?_); rw [map_smul, drip_apply, Finset.smul_sum,sum_read]; simp_rw [smul_smul,smul_read,D_read]
lemma mantleZ (h:F.Unify X u r): (waveLots X).Z=r • ((Φ u).transpose * (waveLots F).Z * Φ u):=by
  let Q:= waveLots F; let Z:=waveLots X
  ext i j; change Z.Z i j=_; rw [← show Z.combo [Place.a i,Place.a j]=Z.Z i j from DFunLike.congr_fun (Z.bookA i j) [],show Z.combo=_ from bookN F u X h]; rw [smul_read, mantle]; simp only [Fintype.sum_sum_type,Receipt.skein,Place.a,mul_zero,zero_mul,add_zero,Finset.sum_const_zero,Matrix.smul_apply,smul_eq_mul]; congr 1
  rw [Matrix.mul_apply]; simp_rw [Matrix.mul_apply,Finset.sum_mul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _=> Finset.sum_congr rfl fun x _=> ?_
  change u.φ x i*u.φ y j* Q.combo [Place.a x,Place.a y]=_*_; rw [show Q.combo [Place.a x,Place.a y]=Q.Z x y from DFunLike.congr_fun (Q.bookA x y) []]; change _=u.φ x i* Q.Z x y *u.φ y j; ring
lemma mantleX (h:F.Unify X u r): (waveLots X).X=r • ((Φ u).transpose * (waveLots F).X * Ψ u):=by
  let Q:= waveLots F; let Z:=waveLots X
  ext i j; change Z.X i j=_; rw [← show Z.combo [Place.k i,Place.c j]=Z.X i j from DFunLike.congr_fun (Z.bookD i j) [],show Z.combo=_ from bookN F u X h]; rw [smul_read,mantle]; simp only [Fintype.sum_sum_type, Receipt.skein, Place.k, Place.c,mul_zero,zero_mul,add_zero,zero_add,Finset.sum_const_zero,Matrix.smul_apply,smul_eq_mul]; congr 1
  rw [Matrix.mul_apply]; simp_rw [Matrix.mul_apply,Finset.sum_mul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _=> Finset.sum_congr rfl fun x _=> ?_
  change u.φ x i*u.ε y j* Q.combo [Place.k x,Place.c y]=_*_; rw [show Q.combo [Place.k x,Place.c y]=Q.X x y from DFunLike.congr_fun (Q.bookD x y) []]; change _=u.φ x i* Q.X x y *u.ε y j; ring
end YM.MSBar.Cutis
