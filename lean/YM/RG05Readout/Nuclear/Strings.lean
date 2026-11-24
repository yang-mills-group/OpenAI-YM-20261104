import YM.RG05Readout.Nuclear.Kite
/-! Tensor generator for patch polynomials. Use finite rank bank at ALL points,
constants depend horizon, slots only, no delta. Norm transfer later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Push.FiniteDetection.Kelvin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {V J:Type}[Fintype V][DecidableEq V]
local notation "Q"=>Complexion E
local notation "U"=>Cloud V
local notation "T!"=> Tensor.T (Cloud V) ℂ
local notation "W"=> Wave V
abbrev chord (a:Q): Q→ₗ[ℂ] Q where
    toFun v:=⟨a.val*v.val, (show ContDiff ℝ ∞ a.val from a.property).mul (show ContDiff ℝ ∞ v.val from v.property)⟩
    map_add' x y:=Subtype.ext <| mul_add (a.val) x.val y.val
    map_smul' x y:=Subtype.ext <| funext fun z=> mul_left_comm (a.val z) x (y.val z)
abbrev core (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E](c:ℂ):Complexion E:= ⟨fun _=>c,(show ContDiff ℝ ∞ (fun _ : E=>c) from contDiff_const)⟩
omit [DecidableEq V] in
lemma tiedC (x y:V→Body): chord (joint Finset.univ x) (joint Finset.univ y)=joint Finset.univ (fun i=> chord (x i) (y i)):=Subtype.ext (funext fun _=>Finset.prod_mul_distrib.symm)
def kitty (V:Type)[Fintype V]:=Submodule.span ℂ (Set.range fun x:V→Body=>joint Finset.univ x)
omit [DecidableEq V] in
lemma ropes (x:V→Body): joint Finset.univ x ∈ kitty V:= Submodule.subset_span (Set.mem_range_self x)
omit [DecidableEq V] in
lemma rope_add (x: V→Body){y: Wave V}(h:y∈kitty V): chord (joint Finset.univ x) y ∈ kitty V:=by
    obtain ⟨f,rfl⟩:= Finsupp.mem_span_range_iff_exists_finsupp.mp (show y∈Submodule.span ℂ _ from h); unfold Finsupp.sum; rw [map_sum]; exact (kitty V).sum_mem (fun i _=>by rw [map_smul,tiedC];exact (kitty V).smul_mem _ (ropes _))
omit [DecidableEq V] in
lemma rope_un {c:ℂ}: core (Cloud V) c∈ kitty V:=by
    let f:= fun _ : V=> core E4 1
    have h:c • joint Finset.univ f=core (Cloud V) c:=Subtype.ext <| funext fun x=> by
       change c*(∏ _i:V,(1:ℂ))= c; simp
    exact h ▸ (kitty V).smul_mem c (ropes f)
-- span code generation, no duplicate bank powers
lemma cord {V:Type}[Fintype V][DecidableEq V](x:Cloud V) : (∑ i:V,∑ j:Axis,(x i j) • (Pi.single i (basis j):Cloud V))=x:=by
    funext i; simp only [Finset.sum_apply,Pi.smul_apply]; rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same]; exact space_expand _
    · intro j _ hj; simp [Pi.single_eq_of_ne (Ne.symm hj)]
    simp
noncomputable def layD (p: T! n) : W :=⟨Tensor.diagonal p,diag_smooth p ∞⟩
lemma rope_D (p:T! n): layD p ∈ kitty V:=by
    induction n with
    | zero=> rw [show layD p=core U (Tensor.diagonal p 0) from Subtype.ext <| funext fun x=>congr_arg p (Subsingleton.elim ..)]; exact rope_un
    | succ n ih=>
       let v:= fun (i:V)(a:Axis)=> layD (p.curryLeft (Pi.single i (basis a))); let f(a:Axis): Body:=⟨fun x=> (↑(x a):ℂ),show ContDiff ℝ ∞ _ from Complex.ofRealCLM.contDiff.comp (PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _ : Axis=>ℝ) a).contDiff⟩
       let XIX(i:V)(a:Axis):V→ Body:=Function.update (fun _:V=>core E4 1) i (f a)
       have hx(i a) : joint Finset.univ (XIX i a) ∈ kitty V:= ropes _
       have he (x:U): Tensor.diagonal p x= ∑ i:V,∑ a:Axis,(chord (joint Finset.univ (XIX i a)) (v i a)).val x:=by
           let y:T! n:= p.curryLeft x; have ht: Tensor.diagonal p x= p.curryLeft x (fun _=>x):=by rw [ContinuousMultilinearMap.curryLeft_apply]; unfold Tensor.diagonal; apply congr_arg; funext i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
           rw [ht]; nth_rw 1 [← cord x]; simp only [_root_.map_sum,map_smul,sum_apply,smul_apply]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro a _
           have hp': (∏ j:V,(XIX i a j).val (x j))= (↑(x i a):ℂ):=by
                rw [Finset.prod_eq_single i]; · rw [show XIX i a i=f a from Function.update_self ..]
                · intro j _ hj; rw [show XIX i a j=core E4 1 from Function.update_of_ne hj ..]
                simp
           change _= (∏ j:V,(XIX i a j).val (x j))* _; rw [hp']; rfl
       rw [show layD p= ∑ i:V,∑ a:Axis,chord (joint Finset.univ (XIX i a)) (v i a) from Subtype.ext <| funext fun x=>by change Tensor.diagonal p x=_; simp_rw [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply];exact he x -- need change
          ]
       exact (kitty V).sum_mem fun i _=> (kitty V).sum_mem fun j _=> rope_add _ (ih _)
-- fixed atoms bank at finite horizons
abbrev Ticket (V:Type)[Fintype V] (n:ℕ):=Fin (Module.finrank ℂ (Tensor.T (Cloud V) ℂ n))
instance tissues (V:Type)[Fintype V](n:ℕ): FiniteDimensional ℂ (Tensor.T (Cloud V) ℂ n):=Module.Finite.of_restrictScalars_finite ℝ _ _
noncomputable abbrev Quill (V:Type)[Fintype V] (n:ℕ): Module.Basis (Ticket V n) ℂ (Tensor.T (Cloud V) ℂ n):= Module.finBasis ℂ _
noncomputable def page (V:Type)[Fintype V](n:ℕ): Tensor.T (Cloud V) ℂ n →L[ℂ] (Ticket V n→ℂ):= (Module.Basis.equivFun (Quill V n)).toLinearMap.toContinuousLinearMap
omit [DecidableEq V] in
lemma pulp (p:T! n): p=∑ i,page V n p i • Quill V n i:=(Module.Basis.sum_repr (Quill V n) _).symm
omit [DecidableEq V] in
lemma song (p:T! n): layD p=∑ i,page V n p i • layD (Quill V n i):=Subtype.ext <| funext fun x=>by
    simp_rw [AddSubmonoidClass.coe_finsetSum,SetLike.val_smul, Finset.sum_apply]; change Tensor.diagonal p x= _; unfold Tensor.diagonal; nth_rw 1 [pulp p]; rw [sum_apply]; rfl
noncomputable def fibre (V:Type)[Fintype V][DecidableEq V](n:ℕ)(i:Ticket V n): (V→Body) →₀ℂ:=(Finsupp.mem_span_range_iff_exists_finsupp.mp (rope_D (Quill V n i))).choose
lemma unravel (V:Type)[Fintype V][DecidableEq V] (n:ℕ)(i:Ticket V n): layD (Quill V n i)= ∑ j∈(fibre V n i).support,(fibre V n i) j • (joint Finset.univ j):=(Finsupp.mem_span_range_iff_exists_finsupp.mp (rope_D (Quill V n i))).choose_spec.symm
end YM.RG05Readout.Nuclear
