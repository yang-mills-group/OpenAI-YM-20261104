import YM.FVAAlt2.First.Beam
/-! Strip common incoming analytic phase for computing the IR fit jet only.
 Does not substitute for the literal cylinder in higher diagrams. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Native MS.Book MS.Plane MS.Theater MS.Landau MS.Landau.Detect MS.Lifting MS.Tone MS.Momentum
open Pert Pert.Orb MS.Cylinder.Lab
open Shop (stripCore hits edge_s ψ onew edge_mask)
open Complex (I)
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}(u:Key G)
local notation "Ω"=> Lane4 G
def loan (p:QP)(b:Axis)(t:ℝ):ℂ:= Tone.bill (t • p) (-(Tone.offset (some b,false)))
lemma payAt (p:QP)(a:Edge Cover)(i:G.ColorIndex) (t:ℝ): loan p a.2 t * Shop.onew (a,i) (hits (ψ a.2 i p) t)= Tone.bill (t • p) (embed a.1):=by unfold loan; change _*paywave (( Landau.gauge a.2,i), t • p) ((Landau.gauge a.2, i), a.1)=_; rw [ Tone.pw, ← rightadd ]; simp [Landau.gauge, add_assoc] -- orientation
lemma dutyLoan(t:ℕ)(x:Edge Cover)(i:G.ColorIndex)(p:QP): reading t (fun v=> loan p x.2 v * onew (x,i) (hits (ψ x.2 i p) v)) = Complex.I^t * (↑((dots G t (speak t x.2 p (cl G i))) x i):ℂ):=by
 simp_rw [payAt, Shop.read_phase]; unfold dots Tensor.diagonal; simp only [LinearMap.coe_mk, AddHom.coe_mk, speak, Theater.wearing]; rw [show fixF (embed x.1)= RG11Scheme.Mesh.row x.1 from PiLp.ext fun b=> Eq.symm (RG11Scheme.Mesh.row_axis _ b)]; simp [amount, Shop.cpar, fixF, cl]; ring
lemma loanAny(x:Edge Cover)(i:G.ColorIndex)(j:Axis)(b:G.ColorIndex)(t:ℕ)(p:QP): reading t (fun v=> loan p j v * onew (x,i) (hits (ψ j b p) v)) = Complex.I^t * (↑(dots G t (speak t j p (cl G b)) x i):ℂ):=by
 rcases eq_or_ne j x.2 with ht|ht; subst j
 · rcases eq_or_ne i b with H|H; · subst b; exact dutyLoan ..
   simp_rw [edge_mask (G:=G) (ψ x.2 b p) (x,i) (show (ψ x.2 b p).1≠(Landau.gauge x.2,i) from fun hz=> H.symm (Prod.ext_iff.mp hz|>.2)),mul_zero]; unfold dots Tensor.diagonal; simp_rw [LinearMap.coe_mk,AddHom.coe_mk,speak,wearing]; simp [cl, H, reading]
 simp_rw [edge_mask (G:=G) (ψ j b p) (x,i) (show (ψ j b p).1≠(Landau.gauge x.2,i) by simp [Landau.gauge,ψ,Tone.Frame.waveForm,ht]),mul_zero]; rw [show dots G t (speak t j p (cl G b)) x=(speak t j p (cl G b)).val x.2 (fun _=> RG11Scheme.Mesh.row x.1) from rfl]; rw [show (speak t j p (cl G b)).val x.2=0 from away _ _ _ ht.symm]; simp [reading]
lemma loan_book (t:ℕ)(b:Axis)(i:G.ColorIndex)(p:QP): reading t (fun v=> loan p b v * tally u (hits (ψ b i p) v) )= Complex.I^t * (↑(wh u (dots G t (speak t b p (cl G i)))):ℂ):=by
 let S:=𝓝[≠] (0:ℝ); let f:=loan p b; have hf: ContDiff ℝ ∞ f:= Lifting.bankForm ..
 let ql (x:paper u.1 × Conn G)(z:ℝ):= f z * onew (x.1.val,x.2) (hits (ψ b i p) z); have he(z:ℝ): loan p b z * tally u (hits (ψ b i p) z)=∑ x:paper u.1 × Conn G,(duke u x:ℂ) * ql x z:=by unfold tally; rw [Finset.mul_sum]; unfold ql f; refine Finset.sum_congr rfl fun x hx=>?_ ; ring
 simp_rw [he]; rw [read_sum (fun j _=>contDiff_const.mul (hf.mul (edge_s (j.1.val,j.2) _))),← duke_wide]; push_cast; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; change reading _ (fun v=> _* ql x v)=_; rw [read_const,show reading t (ql x) =_ from loanAny ..]; ring
lemma rent_sym (i:Ω)(_a:ℕ): ContDiff ℝ ∞ (fun v=>tally u (hits i v)):= ContDiff.sum fun k _=> (edge_s _ _).mul contDiff_const -- a unused remove
lemma firstPage(c: Ω): Rest (fun v=>tally u (hits c v)) ((generation u:ℤ) - wfield c.1) (lamp u c):=by
 rcases c with ⟨⟨⟨_|a,b⟩,t⟩,p⟩ <;> cases b
 case some.false=>
   let c:= ψ a t p; let g:= lamp u c; apply stripCore _ ( loan p a ) (fun v=> tally u (hits c v)) g _ (show ContDiff ℝ ∞ (loan p a) from bankForm _ _) (rent_sym u c 0) (by simp [loan]);
   have he:(generation u:ℤ)- wfield c.1= u.1+1:= by rw [show wfield c.1 = 1 from rfl,generation]; omega
   change Rest (fun v=> loan p a v * tally u (hits c v)) ( (generation u:ℤ)- wfield c.1 ) g; rw [he]; unfold c; refine ⟨(show ContDiff ℝ ∞ (loan p a) from bankForm _ _).mul (rent_sym u c 0),fun h=>by omega,?_⟩; intro j hj; split
   · next h=> obtain rfl:j=u.1+1:= (by omega); rw [loan_book]; change _ = Complex.I^_ * pick u ( _ ); rw [dots_wide];rfl
   next h=> rw [loan_book,dots_small u j (by omega)]; simp only [Complex.ofReal_zero,mul_zero]
 all_goals
   simp only [Theater.lamp, tally, hits, Shop.onew, paywave, formAt ]; simp [Cylinder.way, Theater.RowLeg, Theater.StarView, Theater.shutter, Theater.valueC, Landau.gauge,Lifting.Rest.zero]
lemma stages_One : Fits (origin u) (Theater.orbit G ( MvPolynomial.X u )) 1 (generation u) false := by
 unfold Fits; rw [ Nat.cast_one,shop_eq,cusp]; intro w _; rcases w with _ |⟨c,_|⟨e,l⟩⟩; · exact Rest.zero _
 · simp only [fieldDim, fieldVal,Wire.ray_go, List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,mono]; exact firstPage u c
 simp only [fieldVal,Wire.ray_go,List.map_cons,mono]; exact Rest.zero _
end YM.FVAAlt2.Pairing
