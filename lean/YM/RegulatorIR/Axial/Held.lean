import YM.RegulatorIR.Axial.Glare
import YM.RegulatorIR.Halo.Mica

/-!
# Both W1 symmetries on orbit PT at all finite horizons, no insertion demanded
Dusk m dummy.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {c f:Side}{G:Gauge}{g:ℝ→ℝ}{T U:Orders (Book G f)}{s m :ℕ}
section
variable {K: Matrix (Book G f) (Book G f) ℝ}
variable (R:RangeR G f (beneath K) g s m T U)
def ribbon (p:Signed)(x y:ℝ→ Horizon G f) : Prop:= ∀ᶠ t in 𝓝 0, climb (t • x t) = cane p (climb (t • y t))
variable (h:Glows (scan R.Val 1)){p:Signed}{x y:ℝ→ Horizon G f}
variable (H:ContDiffAt ℝ ∞ x 0)(Ht:ContDiffAt ℝ ∞ y 0)(hg: ribbon p x y)
include h H Ht hg
lemma gilded : money K T y=money K T x:=by
 let P:= fun t=>normalized R.Val 1 t (x t)
 let Q:= fun t=>normalized R.Val 1 t (y t)
 let d:=Laplace.dim G R.E
 suffices hx: Prim.Script (Ward.RangeR.cyclone R y) P by
    apply Ward.RangeR.money_unique R Ht H
    ext1 i; exact congr_fun (Aspiration.unique hx (Ward.RangeR.threaded R H)) i
 intro i; let c:= Ward.RangeR.cyclone R y
 have hq: Bill (i+1) (P-Q):=by
    obtain ⟨C,hC,HH⟩:= h p (d+(i+1)); refine ⟨C,hC,?_⟩
    filter_upwards [HH,hg.filter_mono nhdsWithin_le_nhds,Tested.eventually_pos] with t ht hv hr
    have he:= ht (climb (t • y t)); let k:= scan R.Val 1 t
    let a:=(t^d)⁻¹; have ha:0≤a:=inv_nonneg.mpr (pow_nonneg hr.le _)
    change ‖a*k _ - a*k _‖≤ _; rw [show expLinks G (OEdge f) (t • x t)= _ from hv] -- defin climb?
    rw [← mul_sub,norm_mul, Real.norm_of_nonneg ha]; apply le_trans (mul_le_mul_of_nonneg_left he ha); apply le_of_eq;rw [pow_add];unfold a; field_simp
 change Bill _ (P-peval (term c) i)
 rw [show _-_=(P-Q)+(Q-peval (term c) i) by abel]; exact bill_add hq (Ward.RangeR.threaded R Ht i)
end
variable {W:Type}{M:W→ℕ}{n:Page M→Side}

lemma evolved {X Y:Type}{l:ℝ}{A:Deck l X (Book G f)}{B:Deck l Y (Book G c)}{D: GridStep A B}
 {κ:Horizon G f →ℝ}{μ:Horizon G c→ℝ}{S:StepData c f}{N:Scale}
 (R:RangeR G f κ g s m T U)(h:Glows (scan R.Val 1))(F:Forest S.ratio)(W:Square F)(he:Even f.val)(hc:Even c.val)(H:S.patch.Branches S.kernel G)(C:FitsO D S F N κ μ): ∃ R':RangeR G c μ g s m (D.common T) (D.island m T U), Glows (scan R'.Val 1):= by
 let v:= dropQ S F G; let Z:= nextO (G:=G) S F N; let u := fuse v R.Val Z;let M:= blade (OEdge c) v R.Mark
 have hz: Move (full G f) (full G c) v Z:= cross N S H W hc he
 refine ⟨{ E:=R.E⊕Wind F,slots:=inferInstance,Val:=u,Mark:=M,scalar:= C.recurrent T R.scalar,basis:=R.basis.integrates hz,inscription:= blade_c _ R.inscription,marks:= C.victory R.basis hz R.marks R.inscription,archive1:= continues S N H R.basis (shapeOne (G:=G) (I:=OEdge f) (E:=R.E)) R.archive1 W hc he,archive2:=continues S N H R.basis R.inscription R.archive2 W hc he,turn:=fun t=>?_ }, lantern R.basis S N H he hc R.archive1 h W⟩
 rw [R.turn]; have ht := rung S N H R.basis R.inscription R.archive2 W hc he t; have hp:= rung S N H R.basis shapeOne R.archive1 W hc he t
 change _= rightSum u M t/rightSum u 1 t
 rw [show rightSum u M t = _ from ht, show rightSum u (1:Hook G _ _) t=_ from hp]; exact (mul_div_mul_right (hc:=pow_ne_zero _ (S.penaltyZ_pos (G:=G) (N.beta t/t^2)).ne') _ _).symm
variable {S: Heir n G} (H:Reel S) (T:S.Accounts) (V:H.Follows T)
include V
lemma lode :∀ w:Page M,∃ (g:ℝ→ℝ)(U:Orders (Book G (n w)))(R:RangeR G (n w) (H.spot w) g 0 0 (T.orb w) U), Glows (scan R.Val 1):= by
 refine Page.proves ?_ ?_
 · intro w
   rw [H.flagged]; let i:=Page.opening M w; let F:=H.clock i; let A:Hook G Empty (OEdge (n i)):=0
   have hA:Tune A:= ⟨continuous_const,contDiffAt_const⟩
   obtain ⟨hP,hM⟩:= H.accorded T V w
   have ht: Canvas G F (T.orb i) A (0:Orders (Book G (n i))) 0 0:=by
      refine ⟨hP,fun y=> ?_, T.top_o w,hM,fun e r hr=> False.elim (hr rfl), fun _ _ => symmetric_zero⟩
      ext1 j; rw [pow_zero,one_mul,flavor, PowerSeries.coeff_map,rated_v,inscription, PowerSeries.coeff_mk, show priceMap A=0 from rfl]; simp [packed,Series.Radial.jet]; -- fix
   let he:= H.even i
   refine ⟨goal F A,0,{ E:=Empty, slots:=inferInstance, Val:=startO F,Mark:=A,scalar:=1,basis:=start _ he,inscription:=hA,marks:=ht.founds,archive1:= allowed_top F 1 (fun _ _ _ _=>rfl), archive2:= allowed_top F A (fun _ _ _ _=>rfl),turn:=fun _=>rfl },earth F he⟩
 intro w h;obtain ⟨g,U,R,hR⟩:=h;rw [← T.step_o w]; obtain ⟨p⟩:= H.near w
 exact ⟨g,_,evolved R hR _ (H.landscape w) (H.even _) (H.even _) (H.teeth w) p⟩
end YM.RegulatorIR.Axial
