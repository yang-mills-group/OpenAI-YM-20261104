import YM.SchemeConversionRG11.FirstW.Fade.Dunes
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {T:Itinerary} {c:ℕ→Side} {E F V:Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup V] {G:Gauge} {k a b H L:ℕ} {o r p:StepPath T}{x y z:E4}
abbrev HeadR T i x:=1+Gulf T i x -- name signature
variable {f g:Hall T E}{v:Hall T F}{P:Hall T ℝ}{A B C:Sight T G}
def Leeway (T:Itinerary)(o:StepPath T)(P:Hall T ℝ) := ∃ ε>0,∀ᶠ i in atTop,∀ x:Site (T.period i),P i x≠0 → ε≤ Gulf T i (x-o i)
def Gloam (T:Itinerary)(P:Hall T ℝ)(k:ℕ)(f:Hall T E):= ∃ C>0,∀ᶠ i in atTop,∀ x:Site (T.period i),P i x≠0→ HeadR T i x ^ k*‖f i x‖≤ C
lemma Gloam.settle (hp: Leeway T o P)(hz:sails T o x)(h:Dune T o k f)(he:H≤k): Gloam T P H f:=by
 obtain ⟨ε,hε,Hε⟩:= hp; let R:=‖x‖+2; have hR:0<R:= by unfold R; positivity
 have hx:∀ᶠ i in atTop,Gulf T i (o i) ≤ R:= by
   filter_upwards [(Tendsto.norm hz |>.eventually (ge_mem_nhds (lt_add_one _))), T.cutoff.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1))] with i hi hi'
   exact (limb (x:=Lattice.lift (o i)) (show Jam T (‖x‖+1) i _ from hi)).trans (by dsimp [R]; linarith)
 obtain ⟨C,hC,Hc⟩:= h; let B := (1+R)/ε+1; have hb:0<B:=by unfold B; positivity
 refine ⟨B^H*C/ε^(k-H),by positivity,?_⟩; filter_upwards [Hε,hx,Hc] with i hi hx hc j hj
 let t:=Gulf T i (j-o i); have ht:=hi j hj; change ε≤ t at ht; have hv: 0<HeadR T i j:= by have hv:=gulf_pos T i j; unfold HeadR; positivity
 have hh: Gulf T i j ≤ Gulf T i (o i)+t:=by
   have hv:=reverse_cy j (o i); unfold t Gulf growsOut; rw [←mul_add]; exact mul_le_mul_of_nonneg_left hv (T.positive _).le -- t definition
 have he': HeadR T i j ≤ B*t:= by
   calc _ ≤ 1+R+t:=by unfold HeadR; linarith
        _ ≤ (1+R)/ε*t+ t:=add_le_add_left (le_trans (le_of_eq (show 1+R= (1+R)/ε*ε from (div_mul_cancel₀ _ hε.ne').symm)) (mul_le_mul_of_nonneg_left ht (by positivity))) _
        _ = _:= by unfold B; ring
 have hp : t^H*‖f i j‖≤ C/ε^(k-H):= by
   rw [le_div_iff₀ (pow_pos hε _)]
   have hi:0<t:= hε.trans_le ht; refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le ht _) (by positivity)) ?_; have hh:=hc j; change t^k * _ ≤ C at hh; exact le_trans (le_of_eq (by rw [mul_right_comm, ← pow_add,Nat.add_sub_of_le he])) hh -- Nat
 refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.le he' _) (norm_nonneg _)) ?_; rw [mul_pow,mul_assoc,mul_div_assoc]; gcongr
lemma Gloam.roll (h:Gloam T P k f)(hp:Gloam T P k g): Gloam T P k (f+g):=by obtain ⟨C,hc,H⟩:=h; obtain ⟨D,hD,M⟩:=hp; refine ⟨C+D,by positivity,(H.and M).mono fun i hi x hx=>?_⟩; have he : 0<HeadR T i x:= add_pos zero_lt_one (gulf_pos ..) -- add order
                                                                                                                                            ; refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)) ?_; rw [mul_add]; exact add_le_add (hi.1 x hx) (hi.2 x hx)
lemma Gloam.scale [NormedSpace ℝ E] (h:Gloam T P k f)(r:ℝ): Gloam T P k (r • f) := by
 obtain ⟨C,hc,H⟩:=h; refine ⟨‖r‖*C+1,by positivity,H.mono fun i hi x hx=>?_⟩; simp only [Pi.smul_apply,norm_smul]; rw [mul_left_comm]; exact (mul_le_mul_of_nonneg_left (hi x hx) (norm_nonneg _)).trans (le_add_of_nonneg_right zero_le_one)
lemma Gloam.map₂ [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ V](h:Gloam T P a f)(hp:Gloam T P b v)(L:E→L[ℝ] F→L[ℝ] V): Gloam T P (a+b) (fun i x=> L (f i x) (v i x)):=by
 obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,W⟩:=hp; refine ⟨‖L‖*(C*D)+1,by positivity,(H.and W).mono fun i hi x hx=>?_⟩; let t:=HeadR T i x; have ht:0<t:= add_pos (by norm_num) (gulf_pos ..)
 change t^_ * _ ≤_
 calc t^(a+b) * _ ≤ t^(a+b)*(‖L‖*‖f i x‖*‖v i x‖):= mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _))) (by positivity)
      _ = ‖L‖ *((t^a*‖f i x‖)*(t^b*‖v i x‖)):=by rw [pow_add];ring
      _ ≤ _:= le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (hi.1 x hx) (hi.2 x hx) (by positivity) hC.le) (norm_nonneg L)) (le_add_of_nonneg_right zero_le_one)
-- swerve bound Gloam shift NOT stable. shift legs in Dune, then convert.
def swoopP (T:Itinerary)(A:Sight T G)(s:Cover)(u:Walk) := mailR T (fun i (x:Site (T.period i))=> rail x u (A i)) s
lemma crest_leg (h:CrestS T o k A)(s:Step): Dune T o k (peakC T A s):= by rw [lookC]; exact ((h _).shift _).scale _
lemma crest_loop (h:CrestS T o k A)(a:Walk): Dune T o k (fun i x=> rail x a (A i)):= by
 induction a with
 | nil=> simp only [rail,LinearMap.zero_apply]; exact skyhut
 | cons i w ih=> simp only [rail,LinearMap.add_apply]; refine (crest_leg h i).roll (g:=fun j x=>rail (x+i.vec) w (A j)) ?_; simpa only [mail_vec] using ih.shift i.vec
lemma swerve_capG (he:Leeway T o P)(hz:sails T o x)(h:CrestS T o a A)(hh:H≤a)(u:sails T p y)(e:Leeway T p P)(hp:CrestS T p b B)(hv:L≤b)(w:Walk) (s:Cover): Gloam T P (H+L) (mailR T (fun i x=> swerve x w (A i) (B i)) s):= by
 induction w generalizing s with
 | nil=> refine ⟨1,one_pos,Eventually.of_forall fun i x hx=>?_⟩; simp [mailR,swerve]
 | cons i w ih=>
   let f:=mailR T (peakC T A i) s; let g:=mailR T (fun j x=>rail x w (B j)) (s+i.vec)
   let k:= mailR T (fun j x=>swerve x w (A j) (B j)) (s+i.vec); obtain ⟨L,H⟩:= doubles G.ad
   rw [show mailR T (fun l x=> swerve x (i::w) (A l) (B l)) s=(fun (j:ℕ) (x:Site (T.period j))=>L (f j x) (g j x))+k from funext fun i'=>funext fun x=>by simp only [mailR,swerve_eq,H,f,g,k,peakC, map_add,wrap_vec,Pi.add_apply,add_assoc]]
   exact ((Gloam.settle he hz ((crest_leg h i).shift _) hh).map₂ (Gloam.settle e u ((crest_loop hp w).shift _) hv) _).roll (ih _)
lemma spire_boundG (he:Leeway T o P)(hz:sails T o x)(h:CrestS T o a A)(hh:H≤a)(u:sails T p y)(e:Leeway T p P)(hp:CrestS T p b B)(hv:L≤b)(w:Walk) : Gloam T P (H+L) (fun i x=> spire G x w (A i) (B i)):= by
 have h1:= swerve_capG he hz h hh u e hp hv w 0
 have h2:= swerve_capG e u hp hv hz he h hh w 0; rw [add_comm L] at h2
 have e (f:Hall T G.Color):mailR T f 0=f:=funext fun i=>funext fun x=> by simp [mailR]
 rw [e] at h1 h2; simp only [spire,LinearMap.smul_apply, LinearMap.add_apply,LinearMap.flip_apply]; exact (h1.roll h2).scale _
lemma seat_high (hu:sails T o x)(he:sails T p y)(hp:sails T r z)(h:Leeway T o P)(hx:Leeway T p P)(hz:Leeway T r P)(hg:Shore T o a A)(hq:Shore T p b B)(hy:Shore T r k C)(hr:2≤a)(hn:2≤b)(ht:2≤k)(i j:Step): Gloam T P 6 (SeatD T A B C i j):= by
 have h1:Gloam T P 6 (Dra T A B C i j):= (Gloam.settle h hu (hg.2 i j) (by omega: 2≤ a+1)).map₂ (spire_boundG hx he hq.1 hn hp hz hy.1 ht (icon i j)) (innerSL ℝ)
 have h2:Gloam T P 6 (Dra T B C A i j):= (Gloam.settle hx he (hq.2 i j) (by omega: 2≤ b+1)).map₂ (spire_boundG hz hp hy.1 ht hu h hg.1 hr _) (innerSL ℝ)
 have h3:Gloam T P 6 (Dra T C A B i j):= (Gloam.settle hz hp (hy.2 i j) (by omega: 2≤ k+1)).map₂ (spire_boundG h hu hg.1 hr he hx hq.1 hn _) (innerSL ℝ)
 rw [rateD]; exact (h1.roll h2|>.roll h3).scale _
end YM.RG11.FirstW
