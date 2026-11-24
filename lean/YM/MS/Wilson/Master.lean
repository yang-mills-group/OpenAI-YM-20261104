import YM.MS.Book.Chants
/-!
# Every perturbative order at canonical unscaled symbols

Quantity `originInteract` includes S₂ (and possibly volume constants). Haar
 at unit winding. Spin spacings. Sizes not relevant until shell convolution.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Wilsonian
open Function Filter Set Finset Plane Koszul Cylinder Lab Book Convolve
open Orient Chart Paint Lattice Draft Landau Bare Focus Taylor
variable (G:Gauge)
abbrev W := bosons G idRail (0:Cover)
abbrev H := weightH G (0:Cover)

def core : T (Dot G Cover):= levels 2 (W G)+levels 0 (H G)
lemma presence (h:G.Simple): From (W G).val 2:= by
   refine fromC h (centerB _ _) ?_
   simp [W,bosons,weightW,Sew.art, ropes, GHplus, AHplus,Cylinder.single,atLetter,Draft.DotFlip]; right; change ((gone (0:Lot G Axis)):ℂ)=0; simp [gone,atCart] -- clock
lemma mist (G:Gauge): From (H G).val 0:= by intro l h; omega
lemma garment0 (G:Gauge) : (H G).val []=0:= by simp [H,weightH,onedge,Sew.art,region,Maurer.lac,LocalH.spin_zero] -- alias
lemma at_rest (G:Gauge) : core G 0=levels 2 (W G) 0:= by
   refine add_eq_left.mpr ?_; -- expects other direction
   apply Subtype.ext; ext l; by_cases hl:l=[]; subst l; exact (enough _ (h:=0) rfl).trans (garment0 G); exact strange _ (show (l.length:ℤ) ≠ 0 from by have := List.length_pos_iff.mpr hl; omega)

lemma participates (i:ℕ): Limit (core G i).val (i+2) := Limit.add (Limit.mod _ (i+2)) ((Limit.mod (H G).val ((i:ℤ)+0)).up (by omega))
lemma crisp (i:ℕ): Tuned (core G i) 0:=(TuneModel (sym_all _ _ _) (i+2)).add (TuneModel (sym_h _ _) (i+0))
lemma realm (i:ℕ): Colorless (core G i):= (ColorMod (centerB _ _) (i+2)).add (ColorMod (originH _) (i+0))
lemma observes (i:ℕ): stance (core G i):= scene_add (stance_model (threads _) (i+2)) (stance_model (scene _) (i+0))

variable (n:Side)
lemma witnessD (G:Gauge) : docket n (W G)= Sourced (Chart.rent (drive n)) (colorTerm G (Site n)) (loco (drive n)) (glow G (Site n)):= by
    change (sumHome _).val=_; unfold W; rw [vessel,source]
lemma shiftD (G:Gauge) : docket n (H G)= ink (glow G (Site n)).e0 totalH:= by
    change (sumHome _).val=_; unfold H; rw [garment,allH]
lemma coreQ (h:G.Simple): Mut (Spectrum G) (core G) := by
    rw [whorled]; intro k; refine Eventually.of_forall (fun n=> ?_)
    let X := Spectrum G; let B : Bonded _ _:= X.district (P:=Site n); let L := docket n (W G); let Rj := docket n (H G); let P:= tokenL B.BV true DotFlip; let f:= rankLevel 2 L; let g:=rankLevel 0 Rj;
    let K:= vibes (G:=G) (drive n)
    have he : promote (docket n) (core G)=f+g:= by unfold core; rw [map_add, show promote (docket n) (levels 2 (W G))= f from level_up _ _ _ true,show promote (docket n) (levels 0 (H G))=g from level_up _ _ _ true]
    have he0 := from_total n (presence G h); have hv := from_total n (mist G)
    have ha : rankLevel (2-2) (B.BV L) k + rankLevel (2+0-2) (link B.BV true DotFlip L Rj) k=0:= by
        have hl : B.BV L + link B.BV true DotFlip L Rj=0:= by unfold L Rj; rw [witnessD,shiftD]; exact K.quantum_pay _ nice_totalH (adequacy _)
        change mask (k+0:ℤ) _+ mask (k+0:ℤ) _= _; rw [← map_add,hl,map_zero]
    have hp : link B.BV true DotFlip L L=0:= by unfold L; rw [witnessD]; exact K.classicalGauge _ (rent_s _) (rentGauge _)
    have hs : B.BV Rj=0:= by unfold Rj; rw [shiftD]; exact lap_g ..
    have hf0 : link B.BV true DotFlip Rj Rj=0:= by unfold Rj; rw [shiftD]; exact link_g ..
    have ht h (f:Dot G Cover)(ht:Tuned f 0) : Pure DotFlip false (duty h n f) := by
        let v := Tune.move (wrap n) ht; cases h; exact v.parity ghostParity; change Pure DotFlip false (sumHome _).val; rw [total_uses]; exact (Tune.sum _ (fun i _=> Tune.move (fun x=> i+x) v)).parity ghostParity
    have hh : link B.BV true DotFlip Rj L=link B.BV true DotFlip L Rj:= link_commute _ (ht true (H G) (sym_h _ _)) (ht true (W G) (sym_all _ _ _))
    rw [he]; change B.BV ((f+g) k)+(1/2:ℂ) • pairW P (f+g) (f+g) k=0
    simp_rw [Pi.add_apply,map_add, LinearMap.add_apply, Pi.add_apply];
    rw [show pairW P f f k=rankLevel (2+2-2) (link B.BV true DotFlip L L) k from link_level _ k he0 he0,
        show pairW P f g k=rankLevel (2+0-2) (link B.BV true DotFlip L Rj) k from link_level _ k he0 hv,
        show pairW P g f k=rankLevel (2+0-2) (link B.BV true DotFlip Rj L) k from link_level _ k hv he0,hh,
        show pairW P g g k=rankLevel (0+0-2) (link B.BV true DotFlip Rj Rj) k from link_level _ k hv hv,
        show B.BV (f k)= _ from (lap_level B k), show B.BV (g k)= _ from (lap_level B k), hp,hf0, hs]
    unfold rankLevel; simp only [map_zero,add_zero,zero_add, smul_add]; rw [← add_smul]; norm_num; exact ha -- maybe simp cast
end YM.MS.Native.Wilsonian
