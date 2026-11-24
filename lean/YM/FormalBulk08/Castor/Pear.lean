import YM.FormalBulk08.Trellis.Arch
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Castor
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {I J: Type*}{G:Gauge}{d k D E m n l r e:ℕ}{B:Frame G d}{W:Roof.Plaza B D}{T S:Anthem D G}{o:Loc G 1}
-- general operator. Source-weight part not paid twice.

def crease (F: Frame G d)(T:Roof.Plaza F D)(P:Anthem D G) : Anthem D G:= ∑ i:Letter F, launch (echo F P i) (T i)
def canopy (F:Frame G d)(T:Roof.Plaza F D)(P:Anthem D G): Anthem D G:= P- crease F T P
lemma creaseAt (V:I→ Anthem D G)(Y:Roof.Plaza B D): crease B Y ∘ V=larch Y (pantry B V):=rfl
lemma canFor (V:I→ Anthem D G)(Y:Roof.Plaza B D): canopy B Y ∘ V=V-larch Y (pantry B V):=rfl
lemma crease_cleans (h:Court o B W)(hp:Clef o T l): Clef o (crease B W T) l:= Clef.sum Finset.univ _ (fun i _=> launch_cut _ (h.officers i) (fun k he=> voice_yields B hp.fare i k he))
lemma crease_echo (h:Court o B W) : echo B (crease B W T)=echo B T:= by
    let p(_:Unit):= T; let i':Unit:=()
    change (pantry B (larch W (pantry B p)) · i') = echo B T
    rw [pantry_handle B _ (l:=d) (fun i=> (h.officers i).fare.through (slotsFits ..)),h.salary,Matrix.one_mul]; rfl
lemma canopy_nav (h:Court o B W)(hp:Clef o T l): Clef o (canopy B W T) l ∧ echo B (canopy B W T)=0:= by
    unfold canopy; have he:= crease_cleans h hp
    refine ⟨hp.sub he,funext fun i=>?_⟩; rw [chalk_less _ _ he.fare hp.fare,crease_echo h,sub_self];rfl
lemma crease_plus (_h:Court o B W)(hp:Clef o T l)(hv:Clef o S r): crease B W (T+S)=crease B W T+ crease B W S:= by
    unfold crease; rw [etched_add B hp.fare hv.fare,← Finset.sum_add_distrib];exact Finset.sum_congr rfl fun i _=>launch_add ..
lemma crease_launch (p:Pence)(h: Wade o T l): crease B W (launch p T)= launch p (crease B W T):= by
    unfold crease; rw [launch_ship]; exact Finset.sum_congr rfl fun i _=>by rw [etched_launch B p h,launch_launch]
lemma decay_scale (c:ℝ)(h: Wade o T l): canopy B W (c•T)=c•canopy B W T := by unfold canopy; rw [smul_sub,←launch_C c T, crease_launch _ h, launch_C,launch_C]
lemma recup [Fintype I](Y:I→ Anthem D G)(Q:Matrix I J Pence)(_h:Court o B W) (hp:∀ i,Wade o (Y i) l): canopy B W ∘ (larch Y Q)=larch (canopy B W ∘ Y) Q:= by
    rw [canFor _ W,pantry_handle B Q hp, canFor _ W,←larch_circuit W _ Q]; funext x; rw [Pi.sub_apply]; unfold larch; rw [←Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ;funext p j k; simp_rw [Pi.sub_apply,Kemp.launch, surf,Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
lemma departure {Q:Matrix (Letter B) I Pence} (h:Court o B W): canopy B W ∘ larch W Q=0:= by rw [canFor,pantry_handle B Q (fun i=> (h.officers i).fare.through (slotsFits ..)), h.salary, Matrix.one_mul, sub_self]
lemma sail_can (h:Court o B W)(hp: Clef o T l)(he:Clef o S m): canopy B W (T+S)=canopy B W T + canopy B W S:= by unfold canopy;rw [crease_plus h hp he];abel
lemma qualCrease (Y:Roof.Plaza B D) (T:Anthem D G)(η:ℝ)(h:∀ i, Qual (Y i) o E η): Qual (crease B Y T) o E η := qual_larch Y (pantry B (fun _:Unit=>T)) () h
lemma qualCan (Y:Roof.Plaza B D)(T:Anthem D G)(η:ℝ)(h:∀ i,Qual (Y i) o E η)(he:Qual T o E η): Qual (canopy B Y T) o E η:= qual_sub he (qualCrease Y T η h)
end YM.FormalBulk08.Castor
