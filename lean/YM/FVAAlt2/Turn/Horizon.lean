import YM.MS.Wilson.Growth
import YM.MS.Menus.Tape
/-!
 BV measure bracket/y-frame under s∈H. No rotation of undeclared ghost
 stencils after high calculation performed. `$style` may be oriented only
 MOD translations. Invariant insertions are exact. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.City
open Set Filter Function Finset MeasureTheory Metric
open Plane Koszul Flux Landau Native Wilsonian Chart Draft Lattice Bare Focus Cylinder Lab Taylor Paint Orient Color Tone
open Book Convolve Program Logarithm
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge}{i:ℂ}{m n:ℕ}{q:ℤ} (s:Signed){R:Type}[AddCommGroup R][One R]{F H: Dot G (Four R)}
local notation "P"=> Four R
local notation "A"=> Branch G Axis
lemma poses_limit (h:Limit F.val q) : Limit (pose s F).val q:= by
 unfold pose; apply Limit.shades _ ?_ _; exact fun x hx=> mul_eq_zero_of_right _ ( h x hx )
lemma tune_H (h:Tuned F q): Tuned (pose s F) q := by
   have hx: Tuned (graffiti (σ s) F) q:= h.self_cash (fun i=>by unfold σ; simp only [Complex.star_def,Complex.conj_ofReal]); let g:= graffiti (σ s) F; unfold pose; refine ⟨ (ferry_tie (R:=ℂ) _ (p:=DotFlip) (q:=DotFlip) (fun i=> (pos_par s i).symm)).sym _ hx.symm, hx.ghost.ferry (v:=ghostNo ∘ Prod.fst) (turn s) (by rintro ⟨⟨⟨_|a,_|_⟩,j⟩,x⟩ <;> rfl ) g, hx.still.passes _ g ⟩ -- fill argument
   
lemma pose_gate (F:Dot G P)(i: LightMode G P): enter (turn s i) (pose s F)= (σ s i) • pose s (enter i F):= by unfold pose; rw [LinearMap.comp_apply,ferry_units (turn s) _ ( (axise s).injective ), tagged_s,map_smul]; rfl -- spelling

lemma brush_p (u:G.El) (F:Dot G P) : dye u (pose s F)=pose s (dye u F):= by
 apply Subtype.ext; funext l; induction l generalizing F with
 | nil=> simp [dye,paint,pose,Cylinder.tagged] -- lemma
 | cons i l ih=>
     obtain ⟨i,rfl⟩:= (axise s).surjective i; change (enter (turn s i) (dye u (pose s F))).val l=(enter (turn s i) (pose s (dye u F))).val l; rw [pose_gate]; obtain ⟨⟨⟨i,b⟩,j⟩,x⟩:=i
     have he(k:G.ColorIndex) : turn s (R:=R) (((i,b),k),x)= (((i.map s.perm,b),k), s.act x+ (i.elim 0 (fun a=>shiftTerm s a))) := by cases i<;> simp [turn,purse]
     rw [he]; simp_rw [solok,map_sum,map_smul, ← he, pose_gate, Finset.smul_sum]; rw [sum_stack,sum_stack]; simp_rw [ Finset.sum_apply, smul_stack,Pi.smul_apply  ]; apply sum_congr rfl; intro i hi;
     rw [map_smul,smul_stack, Pi.smul_apply, ih]; unfold σ; exact smul_comm .. -- replace

lemma pose_color (h:Colorless F): Colorless (pose s F):= by intro i; rw [brush_p,h i]
lemma lamp_w (b:Bool) (F:Dot G P) : twisted DotFlip b (pose s F)=pose s (twisted DotFlip b F):= by simp only [pose,LinearMap.comp_apply,← ferry_twist _ (fun i=> (pos_par s i).symm), tag_sign]
variable (F H)
omit [AddCommGroup R][One R] in lemma feesC (i: LightMode G P): σ s i*σ s i=1:= by rcases i with ⟨ ⟨⟨_|i,b⟩,j⟩,a⟩; exact one_mul _; cases h:s.flip i <;> simp [σ,fee,h]
lemma gate2 (i j: LightMode G P)(hv:σ s i=σ s j) : enter (turn s j) (enter (turn s i) (pose s F))= pose s (enter j (enter i F)):= by rw [pose_gate, map_smul,pose_gate, smul_smul,hv, feesC s,one_smul]
def sizeX (a:Axis) : P ≃ P:= (s.actEquiv (R:=R)).toEquiv.trans (Equiv.addRight (shiftTerm s a))
section
variable [Fintype R]
local notation "Β" => Spectrum G
lemma v_branch (a:Axis)(j l:G.ColorIndex) : heart (anti (s.perm a),j) (Landau.gauge (s.perm a),l) (pose s F)=pose s (heart (anti a,j) (Landau.gauge a,l) F):= by rw [heart_all,heart_all,← Equiv.sum_comp (sizeX s a),map_sum]; exact sum_congr rfl fun z _=> gate2 s F ((anti a,j),z) ((Landau.gauge a,l),z) rfl
lemma c_branch (j l:G.ColorIndex) : heart (gaugeC,j) (ghost,l) (pose s F)= pose s (heart (gaugeC,j) (ghost,l) F):= by rw [heart_all, heart_all, ← Equiv.sum_comp (s.actEquiv (R:=R)).toEquiv,map_sum]; exact sum_congr rfl fun z _=> gate2 s F ((gaugeC,j),z) ((ghost,l),z) rfl
lemma reflect_L : (Spectrum G).Lap (pose s F)= pose s ( (Spectrum G).Lap F ):= by
    simp_rw [Bonded.lap_at,Fintype.sum_sum_type,Fintype.sum_prod_type]; simp only [show ∀ (i:Axis)(j:CI G),((Spectrum G).fee (Sum.inl (i,j)):ℂ)=1 from fun i j=>rfl,show ∀ j:CI G,((Spectrum G).fee (Sum.inr j):ℂ)=-1 from fun i=>rfl, one_smul, map_add,map_sum,map_smul]
    refine congr_arg₂ (· + ·) ?_ (sum_congr rfl (fun j _=>congr_arg ((-1:ℂ) • ·) (c_branch s F j j))); rw [← Equiv.sum_comp s.perm]; exact sum_congr rfl fun a _=> sum_congr rfl fun j _=> v_branch s F a j j
lemma root_f (F H:Dot G P) :(Spectrum G).touch F H= ((Β).Lap (couple DotFlip (sumHome F) H)-couple DotFlip ((Β).Lap (sumHome F)) H)-couple DotFlip (twisted DotFlip true (sumHome F)) ((Β).Lap H):= by apply Subtype.ext; simp only [(Spectrum G).t_here,Spectrum,Bonded.lap_here,coupled,twistp,Submodule.coe_sub,link]
lemma touch_H : pose s ((Spectrum G).touch F H)= (Spectrum G).touch (pose s F) (pose s H):= by rw [root_f,root_f]; simp_rw [moving_total,map_sub, ← reflect_L, pose_s,← lamp_w,reflect_L]
lemma same_root {U V:Dot G P}(h:sumHome U=sumHome V): (Spectrum G).touch U F=(Spectrum G).touch V F:= by rw [root_f,root_f,h]
end
lemma reflect_Lcover (F: Dot G Cover) : pose s ((Spectrum G).Lap F)=(Spectrum G).Lap (pose s F):= by
 apply (markEq ..).mp; filter_upwards [soon_heart (Spectrum G) (pose s F), soon_heart (Spectrum G) F] with n hn hf; rw [travel_t,hf,hn,travel_t, reflect_L]
lemma reflect_cover (F H:Dot G Cover) : pose s ((Spectrum G).touch F H)=(Spectrum G).touch (pose s F) (pose s H):= by
 apply (markEq ..).mp; filter_upwards [soon_root (Spectrum G) (pose s F) (pose s H),soon_root (Spectrum G) F H] with n hn hN; rw [travel_t,hN,hn,travel_t,travel_t,touch_H]
lemma touch_recover {F H X:Dot G Cover}(h:BulkTest F H): (Spectrum G).touch F X=(Spectrum G).touch H X:=by apply (markEq ..).mp; filter_upwards [h,soon_root (Spectrum G) F X, soon_root (Spectrum G) H X] with n hh hp he; rw [hp,he]; exact same_root _ (Subtype.ext hh)
-- rank premise for style is already modulo Landau even at arbitrary dimension. No estimation here.
lemma reflect_style (p:Team)(x:ℝ)(F:Dot G Cover): pose s ((Spectrum G).touch ( style G p x n ) F)= (Spectrum G).touch (style G p x n) (pose s F):=by rw [reflect_cover]; exact touch_recover (core_circle G p|>.stance0 x n rfl s)
variable (p:Team)(x:ℝ)(i:ℕ)
open PowerSeries (coeff)
local notation "V"=> fieldV p x
lemma prices_train (k:Signed)(F:Dot G Cover) : pose k (train (V∘Prod.fst) i F)=train (V ∘Prod.fst) i (pose k F):= by
       have hb (k:Signed)(j:LightMode G Cover) : V (turn k j).1=V j.1:= by rcases j with ⟨⟨⟨_|j,t⟩,u⟩,x⟩ <;> rfl
       have hc : graffiti (σ k) (train (V∘Prod.fst) i F)=train (V∘Prod.fst) i (graffiti (σ k) F):= Subtype.ext (funext fun _=>mul_left_comm ..)
       unfold pose; rw [LinearMap.comp_apply,hc]; exact pennant_ferry (turn k) (coeff i) (V∘Prod.fst) (V∘Prod.fst) (fun t=> (hb k t).symm) _
lemma wob_train (F:T (Dot G Cover)) : (pose s) ∘ wobble G p x F = wobble G p x ((pose s) ∘ F):= by
   funext n; unfold wobble; simp only [Function.comp_apply, LinearMap.comp_apply,rolls,map_sum,Program.rules]; simp only [prices_train,map_smul]
end YM.MS.FVA.City

