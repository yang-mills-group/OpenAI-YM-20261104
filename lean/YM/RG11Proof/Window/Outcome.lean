import YM.RG11Proof.Window.Line
import YM.RG11Proof.Bearing.Report

/-! # Kinetic-independent conventional-scheme output in FPS

Default MSB Landau and WilsonX measurement convention per PINS (stress
signals Table normalized plus sign, candidate no engineering-zero part,
Ward at full position length x/point pin; β sign). Bind constructions
separately; any measured/pre-adjustment answers need conversion including
vacuum and W_N leading orientation. Does not eliminate CONTACT lifts.
This endpoint exposes the transcription laws; finite constraint inverse is
in L as in Direction (no implicit h upward); require only through n in some
parts, endpoint uses all orders constructors on A and B. All dependencies
exactly those of the release Frames, independent regulator rate cofinal
consumer supplied (see Brush High etc, currency k=alpha).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Window
open PowerSeries YM.RG11.Jets YM.RG11.Fields YM.RG11.Scale Labels Maxwell YM.PertExtension.Position
open scoped Classical ContDiff BigOperators
variable {G:Gauge}{F:Frames G}(A:ShapeReport G F)

structure Belts (A:ShapeReport G F) where
   ratio:AxisData A
   center : Stress.psStress (tower F 4).toBasis
   hue (k): piece k center∈Stress.candidate (tower F 4)
   flux (n)(χ:E4→ℝ)(h:Table.Window (UVNext.FreeStress.camera 0) χ): Stress.Signals A (tower F 4).toBasis center n h
   arrows(d:ℕ): Arrow.lane (tower F d).toBasis (tower F (d+1)).toBasis
   ways(d i:ℕ): Arrow.Arrives A (tower F d).toBasis (tower F (d+1)).toBasis (rise F d.le_succ) (arrows d) i

structure Forecast (A B:ShapeReport G F)(T:Belts A)(M:Belts B) (p:PowerSeries ℝ) (X:∀i,SquareAt F i):Prop extends Direction A T.ratio B M.ratio p X where
   illuminated: M.center * X 4= subs p T.center
   derives (d:ℕ)(a:Axis): M.arrows d a * X (d+1)=X d * subs p (T.arrows d a)
   position (d n : ℕ){r:ℕ}(v:Fin r→ Pert.Position.E F d)(f:Test r):Through n (B.answers f v) (A.predictions (tower F d).toBasis ⟨p,X d⟩ f v)
   -- scaling at anchors if primary h≥6

 theorem anticipate (hG:G.Simple)(χ:E4→ℝ)(hχ:Table.Window (UVNext.FreeStress.camera 0) χ)
      (B:ShapeReport G F)(T:Belts A)(M:Belts B){p:PowerSeries ℝ}{X:∀ i,SquareAt F i}(h:Direction A T.ratio B M.ratio p X): Forecast A B T M p X:=by
   refine { toDirection:=h, derives:=?arr,illuminated:=?cen,position:=?posi }
   case arr=>
     intro d a
     let z:=rise F d.le_succ
     have H(n:ℕ):MatThrough n (M.arrows d a * X (d+1)) (Horizon.take z (X (d+1))*subs p (T.arrows d a)):=
        Arrow.intertwine A _ _ z B ⟨p,X (d+1)⟩ (holds d.le_succ (h.legal (d+1)).field) (h.legal (d+1)).ruler.base (by convert! (h.legal (d+1)).field.baseline) (by rw [h.match_all]; exact fun _=>Through.refl _)
          (T.ways d n) (M.ways d n) a
     ext i j k; have he:=H k; rw [show Horizon.take z (X (d+1))=_ from h.travels d.le_succ] at he
     exact he i j k le_rfl
   case cen=>
     ext i j k
     have he (q):graded (grade F 4) (piece q (X 4)):=graded.piece_all (w:=grade F 4) (A:=X 4)|>.mp (fun e=>h.graded_X 4 e) q
     exact Stress.lining A B (tower F 4) hG hχ ⟨p,X 4⟩ (h.legal 4).ruler.base (h.legal 4).field (by rw [h.match_all 4]; exact fun _=>Through.refl _) (fun g _ {a b} hv=> @he g a b hv) (fun g _=>T.hue g) (fun g _=>M.hue g)
       (T.flux k χ hχ) (M.flux k χ hχ) i j k le_rfl
       -- binder issue
   case posi=> intro i n r v f; apply ShapeReport.along_all_fields B _ (h.legal i).ruler.base _ f v; rw [h.match_all i]; exact fun _=>Through.refl _

 theorem dual {B:ShapeReport G F}(T:Belts A)(M:Belts B)(hG:G.Simple)(ha:A.table 1 6 3 Pert.Triangle.profileChoice (Pert.Triangle.basic F)=Pert.Triangle.cTest G){α:Type*}(hw:Bridge.High (A.mesh B) α):
   ∃ (t f:PowerSeries ℝ)(X Z:∀ i,SquareAt F i),
      PowerSeries.subst t f=PowerSeries.X ∧ PowerSeries.subst f t=PowerSeries.X ∧
      Forecast A B T M t Z ∧ Forecast B A M T f X ∧ ∀ i,Z i*subs t (X i)=1 ∧ X i*subs f (Z i)=1:=by
   obtain ⟨t,f,X,Z,ht,hf,h1,h2,h3⟩:= full_system A B T.ratio M.ratio hG ha hw
   obtain ⟨χ,hχ⟩:= Work.A01.exists_window (UVNext.FreeStress.camera 0) (UVNext.FreeStress.shutter 0)
   exact ⟨_,_,_,_,ht,hf,anticipate A hG χ hχ B T M h1,anticipate B hG χ hχ A M T h2,h3⟩
end YM.RG11.Window
