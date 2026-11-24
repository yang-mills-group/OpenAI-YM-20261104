import YM.Integration.WilsonAddressedPublicOrderedQuadrature

/-! Take the selected physical limit of the same reflected Wilson measurements and of their cutoff-dependent projected fields. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
namespace YM.Integration.WilsonAddressedPublicNamedQuadrature
open Function Filter Finset Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table Table.Pairing Extraction.Banks RG17 PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonAddressedPublicSelfPurchase (source)
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{r:Fin 2→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin 2→Fin (D+1))(v:∀i,S.Field (d i).val)
local notation "C" => R.family
local notation "caps" => grades (d 0).val (d 1).val


def value (ax:Axis)(site:ℕ)(o:Fin 2→ Cover):ℂ:=
  S.classMoment S caps (Extraction.Order.grid (C) site o)
    (Fin.cons (α:=fun k=>S.Field (caps k)) (S.adj F.room.kernel.spin (d 0).val ax (v 0)) (fun _=>v 1))

theorem physical_limit (b:Fin 2→Bool)(ax:Axis){L:Type}[Fintype L](site:ℕ)(o:L→Fin 2→ Cover)(μ:L→ℂ)
    (below:(l:Filter (ℕ×ℕ))≤f.fuse)(safe:∀a,Extraction.Order.grid (C) site (o a)∈YM.generic 2):
    Tendsto (fun w:ℕ×ℕ=>∑a,μ a*physical caps site (o a) w.1 w.2 (source R F B d v b ax w))
      (l:Filter (ℕ×ℕ)) (𝓝 (∑a,μ a*value R F d v ax site (o a))):=by
  classical
  apply tendsto_finsetSum
  intro a _
  apply Tendsto.const_mul
  let arm:=fun i=>((B i).rows (d i)).arm (b i) (v i)
  let y:=WilsonOriginalBlissMixedGram.columns R ax (d 0).val (d 1).val (arm 0).label (arm 1).label
  have cv:∀k,Tendsto (fun w=>(source R F B d v b ax w) k) (l:Filter (ℕ×ℕ)) (𝓝 (y k)):=by
    intro k
    fin_cases k
    · change Tendsto (fun w=>((C).book.mirrorGroup (d 0).val (Signed.mirror ax)) (star ((arm 0).source w))) _ _
      exact ((C).book.mirrorGroup (d 0).val _).continuous_of_finiteDimensional.continuousAt.tendsto.comp
        ((arm 0).approaches.star)
    · exact (arm 1).approaches
  have native:=Cards.variation (d:=caps) (o a) F.room.generic (safe a) y (source R F B d v b ax) cv below
  have proj:(fun k=>S.project (caps k) (y k))=Fin.cons (α:=fun k=>S.Field (caps k))
      (S.adj F.room.kernel.spin (d 0).val ax (v 0)) (fun _=>v 1):=by
    funext k
    fin_cases k
    · change S.project (d 0).val ((C).book.adj (d 0).val ax (arm 0).label)=_
      rw [←S.adj_project F.room.kernel.spin,(arm 0).represents]
      rfl
    · exact (arm 1).represents
  have same:=S.class_agrees S F.room.kernel.laws.toSymmetric (fun _:ℕ=>le_rfl) caps (generic_conf 2 (safe a)) y
  change Tendsto _ _ (𝓝 (S.classMoment S _ _ _))
  rw [←proj,same]
  exact native

theorem projected_limit (b:Fin 2→Bool)(ax:Axis){L:Type}[Fintype L](site:ℕ)(o:L→Fin 2→ Cover)(μ:L→ℂ)
    (below:(l:Filter (ℕ×ℕ))≤f.fuse)(safe:∀a,Extraction.Order.grid (C) site (o a)∈YM.generic 2):
    Tendsto (fun w:ℕ×ℕ=>∑a,μ a*publicValue (S:=S) caps site (o a) (source R F B d v b ax w))
      (l:Filter (ℕ×ℕ)) (𝓝 (∑a,μ a*value R F d v ax site (o a))):=by
  classical
  let pub (w:ℕ×ℕ):=∑a,μ a*publicValue (S:=S) caps site (o a) (source R F B d v b ax w)
  let group (w:ℕ×ℕ):=∑a,μ a*physical caps site (o a) w.1 w.2 (source R F B d v b ax w)
  have small:Tendsto (fun w=>pub w-group w) (l:Filter (ℕ×ℕ)) (𝓝 0):=by
    rw [Metric.tendsto_nhds]
    intro ε ep
    let M:ℝ:=∑a,‖μ a‖
    have mp:0<M+1:=by dsimp [M];positivity
    have fit:∀ᶠ w:ℕ×ℕ in f.fuse,site≤w.1:=by
      rw [Extraction.Order.fused]
      exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop site
    have measured:=WilsonAddressedPublicOrderedQuadrature.original R F B d (fun i _=>v i) site o safe (div_pos ep mp)
    filter_upwards [fit.filter_mono below,measured.filter_mono below] with w live hear
    have expense:=hear ax b μ live
    simp_rw [WilsonAddressedPublicOrderedQuadrature.at_grid R d live] at expense
    rw [dist_zero_right,norm_sub_rev]
    refine lt_of_le_of_lt expense ?_
    change M*(ε/(M+1))<ε
    rw [←mul_div_assoc]
    exact (div_lt_iff₀ mp).mpr (by linarith)
  have measured:Tendsto group (l:Filter (ℕ×ℕ)) (𝓝 (∑a,μ a*value R F d v ax site (o a))):=
    physical_limit R F B d v b ax site o μ below safe
  simpa only [zero_add,sub_add_cancel] using small.add measured

end YM.Integration.WilsonAddressedPublicNamedQuadrature
end
