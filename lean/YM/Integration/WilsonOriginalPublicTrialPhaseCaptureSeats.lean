import YM.Integration.WilsonOriginalPublicTrialPhaseCopiedCourse

/-! The capture of one product on each original tile pays only its own finite marked roster and its intrinsic pair covers. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCaptureSeats
open Cells Push.GridApprox MergeProof.Accent Marker
open Finset Function Lattice Wilson RG Source Labels Extra.Histories Push Local
open Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Legato GridApprox
open RG05Readout RG05Readout.Many WilsonOriginalPublicTrialPhaseCopiedCourse
open scoped Classical
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G){j c N per:ℕ}
local notation "C" => R.family
local notation "P" => (C).path.rep N per (c+1)
local notation "O" => (C).path.levels.clock.op c per
local notation "V" => Site ((C).side j per)
local notation "load" => Fintype.card I*Fintype.card Signed

theorem restrictSites {n:Side}{U W:Type}[Fintype U][Fintype W](e:W→U)(single:Injective e)
    (o:U→Site n){k:ℕ}(paid:Occupancy o k):Occupancy (o ∘ e) k:=by
  classical
  intro x
  refine le_trans (Finset.card_le_card_of_injOn e (t:=(univ:Finset U).filter (fun v=>o v=x)) ?_ ?_) (paid x)
  · intro a ha;exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩
  · exact single.injOn

theorem pair {n:Side}(t:Tiling n)(i:t.Cell)(B:ℕ)(x y:Site n):
    coverNumber B ({t.copyMap i x,t.copyMap i y}:Support n)=coverNumber B ({x,y}:Support n):=by
  let e:=turnSites (t.omega i) (t.translateBy i)
  have he(u:Site n):e u=t.copyMap i u:=rfl
  simpa only [Finset.image_insert,Finset.image_singleton,he]
    using cover_map e (turn_sep _ _) B ({x,y}:Support n)

theorem original (jc:j≤c)(a:I)(l:ℕ)(o:I→Site ((C).side (c+1) per))(z:I→Site ((C).side c per))
    (parent:(O).ratio.parent ∘ o=z)
    (upper:load≤apron (C).path.levels (c+1))(lower:load≤apron (C).path.levels c)
    (hull:∀k,coverNumber (P).p.B ({o a,o k}:Support _)≤l):
    let site:=(root R (j:=j) (i:=c+1) o)
    Occupancy (fun i:Unit×((V)×I)=>site i.2) (apron (C).path.levels (c+1)) ∧
    Occupancy (fun i:Unit×(V)=>site (i.2,a)) (apron (C).path.levels (c+1)) ∧
    (∀i:(V)×I,coverNumber (P).p.B ({site (i.1,a),site i}:Support _)≤l) ∧
    Occupancy (fun i:Unit×(V)=>site (i.2,a)) (apron (C).path.levels c) ∧
    Occupancy (fun i:Unit×(V)=>(O).ratio.parent (site (i.2,a))) (apron (C).path.levels c):=by
  intro site
  have after(i:(V)×I):(O).ratio.parent (site i)=root R z i:=
    by simpa only [parent] using WilsonOriginalPublicTrialPhaseCopiedCourse.parent R jc o i
  let t:=tilesAt (C).S per (show j≤c+1 by omega)
  let p:=tilesAt (C).S per jc
  have nowSite:site=(fun i:(V)×I=>t.copyMap i.1 (o i.2)):=by
    funext i;simp [site,WilsonOriginalPublicTrialPhaseCopiedCourse.root,jc.trans c.le_succ,t]
  have oldSite:(root R (j:=j) z)=(fun i:(V)×I=>p.copyMap i.1 (z i.2)):=by
    funext i;simp [WilsonOriginalPublicTrialPhaseCopiedCourse.root,jc,p]
  have big:Occupancy site load:=nowSite.symm ▸ WilsonOriginalPublicTrialPhaseTiles.seats t o
  have old:Occupancy (root R (j:=j) z) load:=oldSite.symm ▸ WilsonOriginalPublicTrialPhaseTiles.seats p z
  let drop:Unit×((V)×I)→(V)×I:=Prod.snd
  let fixTile:Unit×(V)→(V)×I:=fun i=>(i.2,a)
  have ds:Injective drop:=fun _ _ eq=>Prod.ext (Subsingleton.elim _ _) eq
  have fs:Injective fixTile:=fun _ _ eq=>Prod.ext (Subsingleton.elim _ _) (congrArg Prod.fst eq)
  refine ⟨fun x=>(restrictSites drop ds site big x).trans upper,
    fun x=>(restrictSites fixTile fs site big x).trans upper,?_,
    fun x=>(restrictSites fixTile fs site big x).trans lower,?_⟩
  · intro i
    rw [nowSite]
    exact (pair t i.1 (P).p.B (o a) (o i.2)).le.trans (hull i.2)
  ·
    have eq:(fun i:Unit×(V)=>(O).ratio.parent (site (i.2,a)))=root R z ∘ fixTile:=
      funext fun i=>after (i.2,a)
    rw [eq]
    exact fun x=>(restrictSites fixTile fs _ old x).trans lower

end YM.Integration.WilsonOriginalPublicTrialPhaseCaptureSeats
end
