import YM.MS.Motif.Pulp

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Native
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ} {F:Rack G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
abbrev spikeV (i:Arts.L n)(x:SectorP n): ℂ:=Complex.I*(x i:ℂ)
lemma spike_δ (i:Arts.L n)(x:SectorP n): δ i x=spikeV i x:= rfl
abbrev at_g (a:Arts.L n)(c:G.ColorIndex): Cfield G n:= ((some a,false),c)
lemma mon_leaf (a:Cfield G n): Book.rank 1 (leaf a):= grade1 (fun _=>_)
lemma mon_apply {q:ℤ}(h: Book.rank q F)(p:SectorP n →+ℂ): Book.rank q (moment p F):= fun l hl=> by rw [moon,h l hl,mul_zero]
lemma rank_α (i j:Arts.L n)(a: G.ColorIndex): Book.rank 1 ( F₀ i j a):= (mon_apply (F:=A n G j a) (mon_leaf _) (δ i)).sub (mon_apply (F:= A n G i a) (mon_leaf _) (δ j))
lemma c_α (a b:Arts.L n)(i:G.ColorIndex)(j:Cfield G n)(p:SectorP n): F₀ a b i [(j,p)]= spikeV a p*(if j=at_g b i then (1:ℂ) else 0) - spikeV b p*(if j=at_g a i then 1 else 0) := by
    unfold F₀ axisP; rw [Pi.sub_apply,Pi.sub_apply,lock,lock]; simp only [rowP,moon,A,lip,leaf,node1, net_cons,add_zero, spike_δ,show net (A:=Cfield G n) ([]:Legs (Shore G n))=0 from rfl]; rfl
lemma f_ref (a b u:Arts.L n)(i j:G.ColorIndex)(p:SectorP n): F₀ a b i [(at_g u j,p)] = if j=i then I*( ( Landau.delta b u (p a) - Landau.delta a u (p b):ℝ):ℂ) else 0:= by rw [c_α]; unfold spikeV at_g Landau.delta; by_cases h:j=i <;> simp [h,mul_ite]; simp only [mul_sub]; by_cases he:a=u <;> by_cases hv:b=u <;> simp [*, eq_comm];
abbrev polar0 (k v a:Arts.L n)(p:SectorP n): ℝ:= Landau.delta v a (p k)-Landau.delta k a (p v)
end YM.MS.Motif
