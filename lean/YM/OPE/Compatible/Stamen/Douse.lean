import YM.OPE.Compatible.Stamen.Loupe
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
abbrev settled (p:Seat k m I):Prop:=∀ i:ℕ, sorted (lilies m k I p i)
lemma tor_fit (p:Seat k m I)(A:RowB I)(h:settled (m:=m) p): settled (m:=m) (lapD A m k p):=by intro i j; rw[pulse_i]; exact congr_arg (fun v:Script I i=> wind i • v) (prop_pad _ (h _) A j)
variable [Fintype I]
def empa (I:Type)[Fintype I](k m:ℕ) :Submodule ℝ (Seat k m (Palette I)) where
      carrier:= setOf fun p=> settled (m:=m) p ∧∀ i:ℕ,(lilies m k _ p i).abides
      zero_mem':=by constructor; intro i; rw [map_zero]; exact fun _=>rfl; intro i; rw[map_zero, Pi.zero_apply]; intro _ _ _ _; simp [scribe]
      add_mem':=fun {p q} ⟨h,hp⟩ ⟨ht,hQ⟩=> ⟨fun i=> by rw [map_add, Pi.add_apply]; exact fun j=> congr_arg₂ (fun (a b:Script (Palette I) i)=> a+b) (h i j) (ht i j), fun i=> by rw [map_add, Pi.add_apply]; intro a n w u; rw[litSum _ (sootS ((sproutV m k p).2 i)) (sootS ((sproutV m k q).2 i)),hp i ..,hQ i ..,add_zero]⟩
      smul_mem':=fun c p ⟨h,hp⟩=> ⟨fun i=>by rw[map_smul,Pi.smul_apply]; exact fun j=> congr_arg (fun a:Script (Palette I) i=> c • a) (h i j),fun i=>by rw[map_smul,Pi.smul_apply]; intro a n w z; rw[score_scaled, hp i ..,mul_zero]⟩
variable {p:Seat k m (Palette I)}(hp: p ∈ empa I k m)
lemma camp (A:RowB (Palette I)) (hp: p∈ empa I k m): lapD A m k p∈ empa I k m:= by
       refine ⟨tor_fit p A hp.1, fun i=>?_⟩; rw[pulse_i]; intro j n w s; rw[score_scaled,beacon _ ((sproutV m k p).2 _) (hp.2 _) A j n w s,mul_zero]
lemma writ (A:RowB (Palette I)) (hp:p∈ empa I k m)(b:ℝ): boostS A b m k p∈empa I k m:=by
      let D:=lapD A m k; have ht (i:ℕ):(D.toLinearMap^i) p∈empa I k m:=by induction i with
                                                                             | zero=>simpa
                                                                             | succ i ih=>rw [pow_succ',End.mul_apply]; exact camp A ih
      rw[boostS,Hflow]; apply Submodule.sum_mem; exact fun i _=> (empa I k m).smul_mem _ (ht _)
end YM.OPE.Silt.Phere
