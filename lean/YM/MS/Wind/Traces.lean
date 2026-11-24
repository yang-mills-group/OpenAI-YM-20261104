import YM.MS.Wind.ToLog
/-!
# POV count for log scales

Mark shorthand with d = coupling base order (0). Includes lack of need
 any smooth Gram. Verified Ward independent. Propagate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge}{p:Team}{φ: Actor G}{F H: Dec G}{u:ℤ}{b:Bool}{n:ℕ} {T:ℝ→ Dot G Cover}{Kx:ℝ→ Law G} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]

lemma feels (c:ℝ)(i:ℕ)(h:∀ x, Sat (Kx x) (F n x) (path c n i H F x)) (hs:Fees b u (F n))(hv:Fees b u (path c n i H F))(w:Wire (BH G) E QP): Domain.Track b (col F n) ((spaceL G).recu i (c:ℂ) (col H) (col F) n) w:= by
   let Z x:= Wiref G (F n x)+ path c n i H F x; have he x: TouchF (Z x):= ((lapid_s (hs.stay x)).sum2 (hv.stay x)).joint; have hl x t := missionday x t H F c n i (hs.stay x|>.joint)
   intro hw; refine ⟨?_,?_,?_⟩; · rintro ⟨x,t⟩; exact (hs.stay x).joint.routine w (exp t)
   · rintro ⟨x,t⟩; unfold Chart; rw [hl x t]; exact (TouchF.scale (↑(exp t):ℂ) (he x)).routine w (exp t)
   intro i' t x j; unfold Domain.tape Chart; rw [hl i' t]; exact dual_log _ _ (hs.stay i'|>.joint) (he i') (fun t=> (h i').2 t) w t j x
lemma closer (v:Dec G) (h:Fees b u (v n)): ∃ r:ℕ, ∀ t, Upper b r (col v n t):= by obtain ⟨r,hr⟩:= h.pay; exact ⟨r,fun t l _ hh=>hr t.1 (exp t.2) l (by omega)⟩
-- `stamp`. 
def kind (G:Gauge): Wind.Flow G →ₗ[ℝ] Wind.Flow G:= LinearMap.pi (fun x=> LinearMap.proj (exp x))
lemma poly_log (h:Ready (F n)): High.stamp (col F n):= Ready.linear h (kind G)
lemma SatSolve (h:G.Simple)(H:PC G p F): Spheres wave (spaceL G) (col F) (col F) ((2:ℂ)⁻¹) 1 true where
   road := fun E _ _ w i hi _=>by rw [show (2:ℂ)⁻¹ = ↑((1/2:ℝ)) from by norm_num]; exact feels (1/2) 1 (fun x=> H.recu i hi x) (H.owes i) (path_c (1/2) i 1 F F (fun _ _=>H.owes _) (fun _ _=>H.owes _)) w
   rank i:= closer F (H.owes i)
   trueC i t:= ((H.owes i).stay t.1).car (exp t.2)
   reflects i t:= ((H.owes i).stay t.1).stand (exp t.2)
   poly i:= poly_log (H.owes i).currency
   qfm n t w hn hP hx:= by
      let x:=t.1; let z:=exp t.2; let A:=payR F x z; let Y:=Ω G z; let X:=Y.C
      have hp:Pass (Mood G z) (A n) μzone:= period0 μzone cour0 (mood_f _) ( (H.owes n).stay x|>.joint)
      have hh:= realized x h H n z w (hx rfl); unfold mat GridR.matCont at hh; change (( (Z G).raise (A n)+orbit (Mood G z) μzone (A n))+(2:ℂ)⁻¹ • pairW X A A n) w=0 at hh; rw [paired,canon_corner (fun i j=>X (A i) (A j)) _ hn, show A 0=0 from centered H x z,map_zero,map_zero,LinearMap.zero_apply,zero_add,zero_add,finite_cc μzone hp] at hh
      rw [Ward,Pi.neg_apply, ← add_eq_zero_iff_eq_neg]; change (Z G).raise (A n) w + (Ccy (Mood G z) (A n) μzone w+ ((2:ℂ)⁻¹ • (∑ i∈Domain.paths n 1,X (A (n-i)) (A i))) w)= _; simpa only [Pi.add_apply,add_assoc] using hh
lemma PMSolve (h:G.Simple)(HM:PC G p F)(hx:PM φ F H 0)(hp: Circle G φ false 0)(he:∀ x, Weightless (Spectrum G) (style G p x) (φ x)): Spheres wave (spaceL G) (col F) (col H) 1 0 false where
   road:= fun E _ _ w i _ _=>by rw [show (1:ℂ)=↑(1:ℝ) from rfl]; exact feels 1 0 (fun x=> hx.recu i x) (hx.owes i) (path_c 1 i 0 F H (fun _ _=> HM.owes _) (fun _ _=>hx.owes _)) w
   rank i:= closer H (hx.owes i)
   trueC i t:= ((hx.owes i).stay t.1).car (exp t.2)
   reflects i t he:= Bool.noConfusion he
   poly i:= poly_log (hx.owes i).currency
   qfm n t w _ _ hw:= by
      let x:=t.1; let z:=exp t.2; let A:=payR F x z; let T' :=payR H x z; let U:=Ω G z; let V:=U.C; let LL:=Mood G z
      have hH:=congr_fun (solidmark x h HM n hx hp (he x) z) w; change ((Z G).raise (T' n) w+orbit LL μzone (T' n) w)+ pairW V A T' n w=0 at hH
      rw [paired,canon_sub (fun i j=>V (A i) (T' j)),show A 0=0 from centered HM x z,map_zero,LinearMap.zero_apply,zero_add, finite_cc μzone (show Pass LL (T' n) μzone from period0 μzone cour0 (mood_f G) ((hx.owes n).stay x).joint)] at hH
      rw [Ward,Domain.recu,Domain.using_tree,one_smul,Pi.neg_apply,Pi.add_apply,← add_eq_zero_iff_eq_neg]; rw [add_assoc] at hH; exact hH
end YM.MS.Wind
