import YM.MS.Menus.Spark
/-!
# Giving polynomial-scale changes rank two

Old minus new. $¹⁄₂a,b+¹⁄₂a$ at order k, native jets.
 All-branch weighted words and measure respect stencil in support, also partial turns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost Detect Detect.Mark Wire
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open PowerSeries (coeff)
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {i j k r:ℕ} (x:ℝ) {p q:Team}
-- convenient formal helper
lemma style_diff (h:∀ i, i<k → p i=q i)(hx:0<k): style G p x k-style G q x k=(coeff k (shift p x)-coeff k (shift q x)) • core G 1 + (train (Y p x) k (core G 0)- train (Y q x) k (core G 0)):= splice x _ (fun i hi=> (h i hi).symm) hx
structure Career (G:Gauge)(p q:Team)(k r:ℕ)(v:ℤ)(H:ℝ→ Law G): Prop where
    past i (h:i<k): p i=q i
    size (x:ℝ): Limit ((style G p x k)-(style G q x k)).val r
    jet (x:ℝ): Fits ((style G p x k)-(style G q x k)) (H x) r v true
lemma ferryPlan {p q:Team}{k:ℕ}(h:∀ i,(p i).waveA=(q i).waveA)(ht:∀ i,(p i).waveC=(q i).waveC)(F:Dot G Cover): train (Y p x) k F=train (Y q x) k F:= by
    rw [show Y (G:=G) p x=Y q x from ?_]; funext l; rcases l with ⟨⟨⟨_|a,_|_⟩,c⟩,L⟩ <;> simp only [Y,fieldV,Function.comp_apply,adap,if_true,Bool.false_eq_true,if_false] <;> first| simp_rw [ht]| simp_rw [h]
lemma buys_cube (p:Team) (h:G.Simple)(hx:1<k){P:ℝ→ℝ}(H:Ready P): ∃ q, Career G p q k 3 4 (fun i=>(P i:ℂ) • LE G 4):= by
   obtain ⟨Q,rfl⟩:= H.scalar
   let q : Team:= fun i=> {p i with coupling:= if i=k then (p i).coupling-Q else (p i).coupling}
   have he i (hi:i<k): p i=q i:= by simp [q,hi.ne]
   have hv x: style G p x k-style G q x k= (↑(Q.eval x):ℂ) • core G 1:= by rw [style_diff x he (by omega),ferryPlan x (p:=p) (q:=q) (fun _=>rfl) (fun _=>rfl),sub_self,add_zero]; congr 1; simp [q,shift, Nat.ne_of_gt hx, show k≠0 from (by omega)]
   refine ⟨q,he,(fun x=> by rw [hv]; exact Limit.smul _ (participates G 1)),fun x=> by rw [hv]; exact Fits.smul _ (bulk_three h)⟩ -- check notation

-- wave S₂ payments at old plus. A^* inverse. mixed signs

lemma train2 (a b: Lane4 G) (p:Team) (x:ℝ) (k:ℕ)(F:Dot G Cover): run (train (Y p x) k F) [a,b] = coeff k (adap p a.1.1 x * adap p b.1.1 x)* run F [a,b]:= by
    unfold run train; let W := (fieldV p x∘ (Prod.fst:Lane4 G→ Branch G Axis)); let V:= (fieldV p x∘ (Prod.fst:LightMode G Cover→ _)); have hz (i:Lane4 G)(j:LightMode G Cover)(h:paywave i j≠0): V j=W i:= Eq.symm (congr_arg (fieldV p x) (in_light i j h))
    rw [← pennantC (coeff k) F V W paywave hz]; simp [flag,W,fieldV]
lemma preset0 (a:Atom Axis)(h:∀ i,i<k→p i=q i): Preset (adap q a x) (adap p a x) k:=fun i hi=> yielding x (k:=i) (p:=q) (q:=p) (fun i' hi'=> (h i' (by omega)).symm) a i (le_refl i)
-- coeff-linear.
lemma expansion (h:∀ i,i<k→p i=q i)(hk: 0<k) (a b:Atom Axis): coeff k (adap p a x*adap p b x)-coeff k (adap q a x*adap q b x)=(coeff k (adap p a x)-coeff k (adap q a x))+(coeff k (adap p b x)-coeff k (adap q b x)):= by rw [next_pair (preset0 x a h) (preset0 x b h) hk, adap0,adap0,mul_one,one_mul]
lemma tweak (h:∀ i,i<k→p i=q i)(hk: 0<k)(b:Option Axis) : coeff k (adap p (b,true) x)-coeff k (adap q (b,true) x)= coeff k (adap q (b,false) x)-coeff k (adap p (b,false) x):= by
   have he := expansion x h hk (b,false) (b,true); have hv (p:Team) : adap p (b,false) x*adap p (b,true) x=1:=by cases b <;> dsimp only [adap,Bool.false_eq_true,if_false,if_true] <;> apply Program.pairs -- check implicit f
   rw [hv,hv,sub_self] at he; linear_combination (norm:=abel) - he -- abel
-- precision Taylor coordinate
lemma baseK (w:QP)(a b:Axis): Rest (fun t:ℝ=> (precision a b (wave (t • w)):ℂ)) 2 (precision a b w:ℂ):= by
   let D (i:Axis)(p:QP):ℂ:= (p i:ℂ); let P (q:QP):ℂ:= (q.sq:ℂ)
   have he (i j:Axis)(q:QP): (precision i j q:ℂ)= (if i=j then P q else 0)-D i q* D j q:= by unfold P precision D delta; split_ifs <;> push_cast <;> ring
   have hs (q:QP) : P q=∑ i:Axis,D i q * D i q:= by simp [D,P,Momentum.sq,pow_two];
   have hP : Rest (fun x:ℝ=> P (wave (x • w))) 2 (P w):=by simp_rw [hs]; exact Rest.sum Finset.univ (fun i _=> (waveFormR w i).mul (waveFormR w i))
   simp_rw [he]; apply Rest.sub _ ((waveFormR w a).mul (waveFormR w b)); split_ifs; exact hP; exact Rest.zero _

-- a scalar impulse writes S_kin and anti
variable {u v: Polynomial ℝ}
def rush (p:Team)(u v:Polynomial ℝ)(k:ℕ): Team:= fun i=> if i=k then ⟨(p k).waveA+u, (p k).waveC+v,(p k).coupling⟩ else p i
lemma rushed {p:Team} (H:i<k): p i=rush p u v k i:= Eq.symm (if_neg H.ne)
lemma rush_diff (hk:0<k): style G p x k-style G (rush p u v k) x k=train (Y p x) k (core G 0)-train (Y (rush p u v k) x) k (core G 0):= by
   rw [style_diff _ (fun _ hi=> rushed hi) hk, show coeff k (shift _ _) - coeff k (shift _ _)=0 from ?_]; swap
   · simp [shift,rush]
   simp
lemma EQ_A (hk:0<k)(a:Axis)(p:Team): coeff k (adap p (Landau.gauge a) x)-coeff k (adap (rush p u v k) (Landau.gauge a) x)= -(↑(u.eval x):ℂ):= by simp [adap, affirmative,rush,Nat.ne_of_gt hk]
lemma EQ_C (hk:0<k)(p:Team): coeff k (adap p ghost x)-coeff k (adap (rush p u v k) ghost x)= -(↑(v.eval x):ℂ):= by simp [adap, affirmative,rush,Nat.ne_of_gt hk] -- ghost alias
end YM.MS.Menus
