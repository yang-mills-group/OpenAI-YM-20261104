import YM.FVA2.Position.Habitat
import YM.FVA2.Full.Costs
/-!
# H rotation for `Cover` stencil generation

These results on `pose` support passing from a choice of mark data at once to
symmetry-compatible choices. Do not reset the coupling or regenerate the prescription
independently for each field.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Wheel
open Function Set Filter Finset Lattice
open MS MS.Koszul MS.Plane MS.Book MS.Native MS.Native.Orient MS.Native.Chart
open MS.Native.Sew MS.Cylinder MS.Cylinder.Lab MS.Landau MS.Color MS.Native.Paint
open MS.Momentum MS.Menus MS.Native.Wilsonian MS.Arts MS.Outlook MS.Tone
open MS.Book.Program MS.Book.Convolve Brass
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{m n:ℕ}{G:Gauge}(s t:Signed){x:ℝ}{a:Axis}{p:Team}
variable {R:Type}[AddCommGroup R][One R]
local notation "Ω"=> pose s
local notation "V"=> Dot G (Four R)
variable {F T': Dot G (Four R)}
lemma stampB {i:ℤ}(hf:Tuned F i): Tuned (Ω F) i:= by
    let G' := graffiti (σ s) F; have ht:Tuned G' i:= hf.self_cash (fun x=>by simp [σ]); exact ⟨ (ferry_tie (turn s) (pos_par s ·|>.symm)).sym G' ht.symm, ht.ghost.ferry (w:=ghostNo ∘ Prod.fst) (turn s) (fun i=>by rcases i with ⟨⟨⟨_|i,b⟩,c⟩,p⟩ <;> cases b <;> rfl) G', ht.still.passes (turn s) G' ⟩ -- pipe syntax
lemma enter_f (F:V)(x:LightMode G (Four R)) : enter (turn s x) (Ω F)= σ s x • pose s (enter x F):= by rw [pose,LinearMap.comp_apply, ferry_units (turn s) _ (axise s).injective, tagged_s,map_smul]; rfl
lemma color_pose (F:V)(q:G.El) : pose s (dye q F)= dye q (Ω F):= by
    let H(x:Atom Axis × (Four R)): (Atom Axis × (Four R)):= match x with| ((none,b),p)=>((none,b),s.act p)| ((some i,b),p)=> ((some (s.perm i),b), (purse s (p,i)).1)
    have hC : graffiti (σ s) (dye q F)= dye q (graffiti (σ s) F):= by
       apply Subtype.ext; funext l; induction l generalizing F with
       | nil=> simp [dye_rep,Cylinder.tagged]
       | cons i l ih=> rcases i with ⟨⟨a,c⟩,p⟩; simp only [D_eval ((a,c),p) (Subtype.val _), ← enterp, tagged_s, solok,map_sum,map_smul, tagged_s,sum_stack, smul_stack, Finset.sum_apply, Pi.smul_apply, ih]; rw [ Finset.smul_sum ]; exact Finset.sum_congr rfl (fun i _=>mul_left_comm ..)
    unfold pose; rw [LinearMap.comp_apply,hC]; exact paint_pass (stripe G _) q _ (turn s) H (fun x j=>by rcases x with ⟨⟨_|i,b⟩,p⟩ <;> rfl) _
lemma Color_w (h:Colorless F): Colorless (pose s F):= by intro u; rw [← color_pose,h u ]
lemma zframe (x:Four R) (a:Axis) : purse s (x,a)=(s.act x+ shiftTerm s a,s.perm a):= rfl
abbrev hair (a:Axis) : Four R≃ Four R:= (s.actEquiv ( R:=R )).toEquiv.trans (Equiv.addRight (shiftTerm s a))
lemma stream (a:Axis)(x:Four R)(b:Bool)(c:G.ColorIndex): turn s ((( (some a,b),c),x): LightMode G (Four R) )= (( (some (s.perm a),b),c), hair (R:=R) s a x):=rfl
omit [AddCommGroup R] [One R] in
lemma chargeS (b:Bool)(x:Four R)(c:G.ColorIndex) : σ s (( (some a,b), c), x)=(sig s a :ℂ):= by unfold σ fee sig; cases he:s.flip a <;> simp [he]
lemma tex (X:V){a:Axis}(x:Four R)(b:Bool)(i:G.ColorIndex): enter (((some (s.perm a),b),i), hair (R:=R) s a x) (Ω X)= (sig s a:ℂ) • pose s ( enter (((some a,b),i), x) X ):= by rw [ ← stream, enter_f,chargeS ]
lemma term_t (X:V)(x:Four R)(b:Bool)(i:G.ColorIndex): enter (((none,b),i),s.act x) (Ω X)= pose s (enter (((none,b),i), x) X):= by rw [show ( ( (none,b),i ),s.act x)=turn s (( (none,b),i), x) from rfl, enter_f]; simp [σ,fee]
-- Δ transforms. Not ignoring harmonics here.Finite.
variable [Fintype R]
lemma pt_h (X:V)(i:Axis)(c:G.ColorIndex) : Ω (heart (anti i,c) (Landau.gauge i,c) X)= heart (anti (s.perm i),c) ( Landau.gauge (s.perm i),c) (Ω X):= by
   simp_rw [heart_all,map_sum]; refine Fintype.sum_equiv (hair s i) _ _ (fun y=>?_); rw [tex s X, map_smul,tex,smul_smul, ← Complex.ofReal_mul, sig_p, Complex.ofReal_one,one_smul]
lemma pt_g (X:V)(i:G.ColorIndex) : Ω (heart (gaugeC,i) (ghost,i) X)= heart (gaugeC,i) (ghost,i) (Ω X):= by
   simp_rw [heart_all,map_sum]; refine Fintype.sum_equiv s.actEquiv.toEquiv _ _ (fun y=>?_); exact Eq.symm (Eq.trans (congr_arg _ (term_t s X y true i)) ( term_t s _ y false i )) -- gaugeC side? see
lemma gleams (X:V): Ω (( Spectrum G ).Lap X)= (Spectrum G).Lap (Ω X):= by
   simp only [Bonded.lap_at, Fintype.sum_sum_type,Fintype.sum_prod_type, show ∀ (i:Axis)(j:CI G),((Spectrum G).fee (Sum.inl (i,j)):ℂ)=1 from fun i j=>rfl,show ∀ j:CI G,((Spectrum G).fee (Sum.inr j):ℂ)=-1 from fun i=>rfl, one_smul,map_add,map_sum,map_smul]; congr 1; · apply Fintype.sum_equiv s.perm; intro i; exact Finset.sum_congr rfl fun c _=> pt_h s X i c
   exact Finset.sum_congr rfl fun i _=> congr_arg (( -1:ℂ ) • ·) ( pt_g s X i )
omit [Fintype R] in lemma shade_h (X:V)(c:Bool): pose s (twisted (field parity) c X)= twisted (field parity) c (pose s X) := by unfold pose; rw [LinearMap.comp_apply, ← tag_sign,ferry_twist (turn s) (fun x=> ( pos_par s x ).symm )]; rfl
lemma pose_h (F H:V) : Ω ((Spectrum G).touch F H)=(Spectrum G).touch (Ω F) (Ω H) := by
    let B:= Spectrum G; let Z:On (Branch G Axis) (Four R) ℂ:= B.Lap
    have he (F H:Dot G (Four R)) : B.touch F H= (Z (couple (field parity) (sumHome F) H)-couple (field parity) (Z (sumHome F)) H)-couple (field parity) (twisted (field parity) true (sumHome F)) (Z H):= by apply Subtype.ext; simp only [B.t_here,B,Z,Spectrum,Bonded.lap_here,coupled,twistp,Submodule.coe_sub,link]
    rw [show (Spectrum G).touch F H= _ from he F H,show (Spectrum G).touch (Ω F) (Ω H)=_ from he ..]; simp only [ B,Z,map_sub,gleams,pose_s, ← moving_total, shade_h ]
variable {A B F: Dot G Cover}
lemma cone_pts : pose s ((Spectrum G).Lap A)= (Spectrum G).Lap (pose s A):=by
   refine (markEq ..).mp ?_; filter_upwards [soon_heart (Spectrum G) (pose s A),soon_heart (Spectrum G) A] with n hn ha; rw [hn, travel_t, travel_t, ha, gleams]
lemma cone_tree : pose s ((Spectrum G).touch A B)=(Spectrum G).touch (pose s A) (pose s B):= by
    refine (markEq ..).mp ?_; filter_upwards [soon_root (Spectrum G) (pose s A) (pose s B),soon_root (Spectrum G) A B] with n hn ha; rw [hn,travel_t,travel_t,travel_t,ha,pose_h]
lemma wind_t (h:stance A): pose s ((Spectrum G).touch A B)=(Spectrum G).touch A (pose s B):=by
    rw [cone_tree]; refine (markEq ..).mp ?_; filter_upwards [soon_root (Spectrum G) (pose s A) (pose s B), soon_root (Spectrum G) A (pose s B), h s ] with n hn hP he; rw [hn,hP]; apply Subtype.ext; rw [ (Spectrum G).t_here, (Spectrum G).t_here, (show (sumHome (shown n (pose s A))).val= (sumHome (shown n A)).val from he) ] -- hi definition docket maybe he type
omit [Fintype R] in
lemma limits_p {F: V} {v:ℤ}(h:Limit F.val v): Limit (Ω F).val v:= Limit.shades (graffiti (σ s) F) (fun l hL=> by change (l.map _).prod*F.val l=_; rw [h l hL,mul_zero]) _ -- rank aware
-- adapted Eras stanceTrain witness on arbitrary action (since Team gives only scalars)
lemma trainE (p:Team)(x:ℝ)(i:ℕ)(F: Dot G Cover): pose s (train (fieldV p x ∘ Prod.fst) i F)= train (fieldV p x ∘ Prod.fst) i (pose s F):= by
    have hb (j:LightMode G Cover): fieldV p x (turn s j).1=fieldV p x j.1:= by rcases j with ⟨⟨⟨_|j,t⟩,u⟩,x⟩ <;> rfl
    have hc : graffiti (σ s) (train ((fieldV p x)∘Prod.fst) i F)=train ((fieldV p x)∘Prod.fst) i (graffiti (σ s) F):= Subtype.ext (funext fun _=>mul_left_comm ..)
    unfold pose; rw [LinearMap.comp_apply,hc]; exact pennant_ferry (turn s) (PowerSeries.coeff i) ((fieldV p x) ∘ Prod.fst) ((fieldV p x) ∘ Prod.fst) (fun t=> (hb t).symm) _
lemma wobPose (T:T (Dot G Cover)): wobble G p x (pose s ∘ T)= pose s ∘ wobble G p x T:= by
 funext n; unfold wobble; simp only [LinearMap.comp_apply,Program.rolls,rules,map_sum,map_smul,Function.comp_apply,trainE] -- may Lean witness
end YM.FVA2.Position.Wheel
