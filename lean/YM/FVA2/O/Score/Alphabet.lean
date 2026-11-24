import YM.FVA2.O.Seam.Loom
import YM.FVA2.Scale.System
/-!
# Coherent physical alphabet for the OPE and complete correlation arrays

Correspondence of graded labels (`Q G` on `portDeck`) to the graded basis
of `XSpace` (`Toon` in `FVA2/Dframe` notation). Recover the label when working
in a larger or smaller allowed measurement horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Score
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open Dframe FVA2.Scale MS.Rake MS.Theater Level
variable { G : Gauge } { I J : Type } {n m k d:ℕ}
local notation "B0"=> Press.portDeck G
abbrev Grade (G:Gauge)(n:ℕ):= Plaid (Press.portDeck G) n
abbrev Q (G:Gauge):= Rake.Label (Press.portDeck G)
abbrev Scan (G:Gauge)(n:ℕ):= Fin n→ Q G
abbrev own (k: Grade G d) : Q G:= ⟨ d,k ⟩
abbrev heft (u:Q G):ℕ:= u.h
abbrev grab (v:Q G):Toon G (heft v):= Land.read v.item
abbrev low (u:Q G)(h:heft u≤d) := Dframe.enroll h (grab u)
lemma low_size (u:Q G)(h:heft u≤d): Glyph.size ( low u h )=heft u:= rfl
abbrev cap (v:Q G)(h:heft v≤d): Sec G d:= theory ( low v h )
lemma under_0 (p:Toon G d): low (Dframe.flash p) ( Dframe.size_le p ) = p:=rfl
lemma under_k (v:Q G)(hr:heft v≤n)(hp:n≤d):enroll hp (low v hr)=low v (hr.trans hp):= rfl
lemma cap_0 (p:Toon G d): cap (Dframe.flash p) (Dframe.size_le p)=theory p:= rfl
lemma flash_c (p:Toon G d): Seam.actor p=Dframe.flash p:=rfl
-- prices per alphabet
abbrev totalG (p:Scan G n): ℕ:= ∑ i, heft ( p i )
abbrev Guarded (u:Scan G n)(d:ℕ): Prop:= ∀ i, heft (u i) ≤ d
abbrev tape (p:Scan G n)(h:Guarded p d): Tags G d n:= fun i=> cap (p i) (h i)
lemma guardT (p:Scan G n): Guarded p (totalG p) := fun _=> Finset.single_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin n)))=> Nat.zero_le (heft (p i))) ( Finset.mem_univ _ )
lemma totalW (p:Scan G n)(v:Scan G m): totalG (Fin.append p v)= totalG p+totalG v:= by unfold totalG; rw [Fin.sum_univ_add]; simp
lemma totalOne (p:Q G) : totalG ( fun _ : Fin 1 => p )= heft p:= by simp [totalG]
-- basis block for sector through grade (including itself)
abbrev coord (i:Toon G d): Sec G d→ₗ[ℂ]ℂ:= (Daylight B0 d).coord i
lemma pivotδ (q p:Toon G d): coord q ( theory p )= if p=q then 1 else 0:= by rw [ ← theory_sig ]; simp only [coord,Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply]
lemma distant (p q:Toon G d)(h:q.size≠p.size): proj (G:=G) q.1 ( theory p )=0:= Eq.trans (congr_arg _ (Level.top p).symm) ( Level.distinct ( theory p ) q.1 p.1 ( fun H=> h (congr_arg Fin.val H) ) )
-- at max grade
abbrev vertex (i:Grade G d): Sec G d:= cap (own i) le_rfl
abbrev paygrade (i:Grade G d): Sec G d →ₗ[ℂ] ℂ:= coord ( grab (own i) )
lemma pivotA (i j:Grade G d): paygrade i ( vertex j )= if i=j then 1 else 0:= by rw [ show paygrade i ( vertex j )= _ from pivotδ (grab (own i)) (grab (own j)) ]; congr! 1; constructor; exact fun h=> Eq.symm ( by exact eq_of_heq ( Sigma.ext_iff.mp h ).2 ); exact fun h=> h ▸ rfl
-- basis sum in exact grade
abbrev at_grade (u:Sec G d): Prop:= proj (⟨d, Nat.lt_succ_self _ ⟩:Level.E d) u=u
def into (k:ℕ) (G: Gauge): Grade G k ↪ Toon G k:={ toFun:=Land.read, inj':= fun _ _ h=> by exact eq_of_heq (Sigma.ext_iff.mp h).2 }
lemma grade_iff (i: Toon G d): i∈ Finset.map ( into d G ) Finset.univ ↔ i.size=d := by
    refine ⟨ fun h=>?_, fun h=>?_⟩; · obtain ⟨u,hu,rfl⟩:= Finset.mem_map.mp h; rfl
    rcases i with ⟨⟨v,hv⟩,i⟩; change v=d at h; cases h; exact Finset.mem_map.mpr ⟨ i,Finset.mem_univ _,rfl ⟩
lemma sink (u:Sec G d)(q p:Toon G d)(h:q.size≠p.size): coord q ( proj p.1 u )=0:= by
    nth_rw 1 [ ← all_sig u ]; simp only [map_sum,_root_.map_smul]; apply Finset.sum_eq_zero; intro i hi; by_cases hp:p.size=i.size; · rw [ show p.1=i.1 from Fin.ext hp, Level.top, pivotδ,if_neg (fun e=> h ( ( congr_arg ( fun s:Toon G d=> s.size ) e.symm ).trans hp.symm )),smul_zero ]
    rw [ distant _ _ hp,map_zero,smul_zero]
lemma whole_grade (u:Sec G d)(hp:at_grade u): (∑ i:Grade G d,paygrade i u • vertex i)=u:= by
    let J:= Level.E d; let i':Level.E d:=⟨d,Nat.lt_succ_self _⟩;
    have h : ∑ i∈Finset.map ( into d G ) Finset.univ,(Daylight B0 d).repr u i • theory i=∑ i:Toon G d,(Daylight B0 d).repr u i • theory i:= by
        apply Finset.sum_subset (Finset.subset_univ _); intro q hq hu; obtain hv:q.size ≠ d:= fun p=> hu ( (grade_iff q).mpr p ); -- if no Grade at d, cannot enumerate it in sink using p.
        have he : coord q u=0:= by
            rw [ ← hp, ← all_sig u ]; simp only [map_sum,_root_.map_smul]; apply Finset.sum_eq_zero; intro i hi; by_cases hz:i'.val=i.size; · rw [ show ( ⟨d,Nat.lt_succ_self _⟩: E d)=i.1 from Fin.ext hz, Level.top, pivotδ, if_neg (fun p=> hv ( ( congr_arg (fun s: Toon G d=> s.size) p.symm ).trans hz.symm )), smul_zero ]; -- i' formatting
            suffices h : proj i' ( theory i )=0 by rw [h,map_zero,smul_zero]
            exact Eq.trans ( congr_arg _ ( Level.top i ).symm ) (Level.distinct _ _ _ (fun h=> hz (congr_arg Fin.val h)))
        exact he ▸ zero_smul _ _ -- repr vs coord
    exact Eq.trans (by rw [← h,Finset.sum_map]; rfl : (∑ i:Grade G d,_) = _) ( all_sig u ) -- inference
end YM.FVA2.O.Score
