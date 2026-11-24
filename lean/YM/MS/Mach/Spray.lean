import YM.Extra.WEAK_SCALING_ACTLAW.Color
import YM.Gauge.Chart
import YM.MS.Halo.Madd
import YM.MS.Heat.Odelta

set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Pilot Garment Color Book
open Motif Halo Native
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {k s n:ℕ} {z:ℂ} {F H:Rack G n} {x y:ℝ→ Rack G n} {U Y:Mield G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄" => product S
abbrev face (k:G.ColorIndex)(t:ℝ): G.El:= G.lieExp (t • baseC k)
lemma prep (i j k:G.ColorIndex): HasDerivAt (fun t=> wc (face k t) i j) (rune k i j) 0:=
   let V: G.Color→L[ℝ] ℂ:= Complex.ofRealCLM.comp ((ContinuousLinearMap.proj (φ:=fun _:G.ColorIndex=>ℝ) j).comp (PiLp.continuousLinearEquiv 2 ℝ _).toContinuousLinearMap);
   V.hasFDerivAt.comp_hasDerivAt (0:ℝ) (Extra.WeakScaling.Color.tangent (baseC k) (baseC i))
lemma zip_p (hs:Zip x F 0)(he:Zip y H 0): Zip (fun t=> x t ⋄ y t) ( F ⋄ y 0+ x 0 ⋄ H ) 0:= by
   intro l; let p:= allocate S l (R:=ℂ); have H0 (i j:Rack G n): (i⋄j) l=p (fun l r=> i l*j r):= scattered _ i j l; simp_rw [Pi.add_apply,H0, ← map_add]; apply gatherZ; intro i j _; exact (hs i).mul (he j)
where
 gatherZ (w:Legs (Shore G n))(V:ℝ→ Shared ( Shore G n ) ℂ)(Y: Shared (Shore G n) ℂ )(h:∀ i j, Split i j w→ HasDerivAt (fun s=> V s i j) (Y i j) 0): HasDerivAt (fun s=> allocate S w (V s)) (allocate S w Y) 0:= by induction w generalizing V Y with| nil=> exact h _ _ .nil| cons a l ih=> exact ih _ _ (fun i j hp=> (h _ _ hp.left).add ((h _ _ hp.right).const_mul _))
local notation "g"=> cwave n G
local notation "Δ"=> Motif.dot (applyS z G n)
def zipC (F:Rack G n)(v:Mield G n): Prop:= ∀ (k:G.ColorIndex), Zip (fun t=> Color.repeatC (face k t) F) ( v k ) 0
lemma spark (hq: Apple U)(k:G.ColorIndex) : zipC (U k) ( fun x=> ∑ j:G.ColorIndex,rune x j k • U j ):= by
   intro v; simp_rw [hq _ _]; apply Zip.sum; intro j hj w; exact (prep j k v).mul_const (U j w)
variable (G n) in
def liftG (z:ℂ) (v:Mield G n): Rack G n:= (-z) • ∑ i:G.ColorIndex,g i ⋄ v i
structure Tail (F:Rack G n)(v:Mield G n) (z:ℂ): Prop where
   guardC: zipC F v
   law:Motif.dot (applyS z G n) F=liftG G n z v
structure Safe (F:Rack G n)(z:ℂ): Prop where
   sym : Symm S F
   even : Pure S false F
   off: fieldSection false F
   pulse:∃ v:Mield G n,Tail F v z
namespace Safe
lemma cpig (c:ℂ)(u:G.El) : repeatC u (coin (A:=Shore G n) c)=coin c:= by rw [← brush, vaultLeaf]
lemma free (c:ℂ): Safe (coin c: Rack G n) z:= by
    refine ⟨ coin_symm _,coin_pure _,fun _ _=>rfl, (0:Mield G n),⟨?_,?_⟩⟩; · intro k; simp_rw [cpig]; exact (fun w=>hasDerivAt_const _ _)
    unfold Motif.dot liftG; rw [ LinearMap.sum_apply]; simp_rw [ coin_v]; simp
lemma lipP (h:Safe F z)(hc:Safe H z): Safe (F⋄ H) z:= by
    obtain ⟨u,hu,HX⟩:= h.pulse; obtain ⟨v,hv,HV⟩:=hc.pulse; refine ⟨h.sym.times hc.sym,h.even.prod hc.even, section_p h.off hc.off, (fun i=>u i ⋄ H+ F ⋄ v i),⟨?_,?_⟩⟩; · intro k; simp_rw [glob_prod]; obtain he :=zip_p ( hu k ) (hv k); simpa only [face,zero_smul,Gauge.mat_lieExp_zero,walk_id] using he -- mismatch z in functions
    unfold liftG at *; rw [Motif.dot_pair (application z) h.even,cross_false',one_smul,HX,HV]; simp only [map_smul, LinearMap.smul_apply,map_add, LinearMap.sum_apply,map_sum, Finset.sum_add_distrib, smul_add]; congr 2; exact Finset.sum_congr rfl (fun i _=> times_assoc (p:=S) _ _ _); apply Finset.sum_congr rfl; intro i _; rw [← times_assoc,h.even.central, times_assoc]
end Safe
lemma Coven (hx:Apple U)(hp:∀ i,Symm S (U i))(ht:Mood false U)(hm: forge Δ U=z • jaw G n U g): ∀ i,Safe (U i) z:= by
   intro i; refine ⟨ hp i,ht.tune i,ht.rank i,_, spark hx i,?_⟩; rw [show Δ (U i)= _ from congr_fun hm i]; simp only [liftG,chew,Pi.smul_apply,map_sum,map_smul]; rw [Finset.sum_comm]; simp_rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; rw [(ht.tune j).central, r_ortho i j]; simp
end YM.MS.Mach
