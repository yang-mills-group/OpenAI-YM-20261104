import YM.OPE.Compatible.Rhus.Scar
import YM.OPE.Compatible.Spa.Toon
/-!
# Physical rank dictionary. Both character axes transported together. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent MeasureTheory RG Wilson Exterior Stationary Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open Module Silt.Float Drift Quit Quit.Jac
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Source Labels Source.Drops WardBin Prairies
open Finset
variable {G:Gauge}{k i r n d m:ℕ}
-- Bundle
abbrev Carton (G:Gauge)(d:ℕ):= (j:Fin (d+1))→ Bead G d j.val × Bead G d j.val
section
variable {e:Fin (d+1)} (j:Fin (e.val+1))
abbrev CoverB (G:Gauge)(d:ℕ)(i: Fin (d+1)):=(Bead G d i.val)×(Bead G d i.val)
noncomputable abbrev BandM (e:ℕ)(h:e ≤ d)(j:Fin (e+1))(G:Gauge):= wallLease (G:=G) (d+1) (show e-j.val+j.val≤d from by omega) (by omega)
def Tacts (j:Fin (e.val+1))(x:CoverB G d e): MixX G j.val (e.val-j.val) (d+1):=(impress x.1 j,impress x.2 j)
noncomputable def Rashi (x:CoverB G d e):Spired G j.val (e.val-j.val) d:= (BandM e.val (by omega) j G).symm (Tacts j x)
lemma thaws (p:CoverB G d e): (BandM _ (by omega) j G) (Rashi j p)= (Tacts j p):=(BandM e.val (show e.val≤d from by omega) j G).apply_symm_apply (Tacts j p)
lemma reveal (p:CoverB G d e): (Rashi j p).val∈ Grade (e.val,j.val):=by
     have he:e.val-j.val+j.val=e.val:= by omega
     exact Eq.mp (congr_arg (fun i=> (Rashi j p).val∈ Grade (i,j.val)) he) ((Rashi j p).property)
lemma relayM (p:CoverB G d e)(x: Jet G): Labels.read x (Rashi j p).val.val= rollReading (d:=d+1) (Tacts j p) (trunk (d+1) x):=by
       let a:= e.val; have h:a ≤ d:= Nat.le_of_lt_succ e.isLt; exact Eq.trans (lease_pay (G:=G) (d+1) _ _ (Rashi j p) x) (congr_arg (fun u:MixX G j.val (e.val-j.val) (d+1) => rollReading u (trunk (d+1) x)) (thaws j p))
lemma Radd (p q:CoverB G d e): (Rashi j (p+q)).val=(Rashi j p).val+(Rashi j q).val:= congr_arg Subtype.val (show Rashi j (p+q)=Rashi j p+ Rashi j q from by unfold Rashi; rw [show Tacts j (p+q)=Tacts j p+ Tacts j q from Prod.ext ((coordinateQ G d e.val j.val).symm.map_add _ _) ((coordinateQ G d e.val j.val).symm.map_add _ _),map_add])
lemma Rsmul (t:ℝ)(p:CoverB G d e): (Rashi j (t • p)).val=t • (Rashi j p).val:= congr_arg Subtype.val (show Rashi j (t • p)=t • Rashi j p from by unfold Rashi; rw [show Tacts j (t • p)= t • Tacts j p from Prod.ext ((coordinateQ G d _ j.val).symm.map_smul _ _) ((coordinateQ G d _ j.val).symm.map_smul _ _),map_smul])
-- map to Label available
noncomputable def CacheM (G:Gauge) (d:ℕ) : Carton G d →ₗ[ℝ] Label G d:={
    toFun p:= ∑ i:Fin (d+1), ∑ j:Fin (i.val+1),(Rashi j (p i)).val
    map_add' p q:=by simp only[Pi.add_apply,Radd,sum_add_distrib]
    map_smul' x p:=by simp only[Pi.smul_apply,Rsmul,Finset.smul_sum]; rfl }
lemma p_R (p:Carton G d): gradePart (e.val,j.val) (CacheM G d p)= (Rashi j (p e)).val:=by
      unfold CacheM; simp only [LinearMap.coe_mk, AddHom.coe_mk,map_sum]; rw [sum_eq_single e,sum_eq_single j]; exact gradePart_self (Rashi j (p e)).val _ (reveal ..); exact fun i _ hi=> gradePart_zero _ _ (e.val,i.val) (by simpa using Fin.val_injective.ne hi.symm) (reveal i (p e)); simp; intro i hi hg; exact sum_eq_zero fun j hj=> gradePart_zero _ _ (i.val,j.val) (Prod.ext_iff.not.mpr fun h=>hg ((Fin.ext h.1).symm)) (reveal j (p i)); simp
lemma ClanM (G:Gauge)(d:ℕ): Injective (CacheM G d):=by
     intro a b h; funext i; let E:= i.val; let p:=a i; let q:=b i; apply Prod.ext; all_goals ext1 j; have hh:Rashi j p=Rashi j q:=Subtype.ext ((p_R j a).symm.trans ((congr_arg _ h).trans (p_R j b)))
     · apply (coordinateQ G d _ j.val).symm.injective; exact congr_arg Prod.fst ((BandM _ (by omega) j G).symm.injective hh)
     apply (coordinateQ G d _ j.val).symm.injective; exact congr_arg Prod.snd ((BandM _ (by omega) j G).symm.injective hh)
end
end YM.OPE.Stroke
