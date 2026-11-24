import YM.Comparison.Stencils.Corona.Fires
import YM.PertExtension.VertexSymbol
/-!
# Operations on cover Wick polynomials and the normalized-jet convention

Wire with booth and compare before quotient. Rotation uses both base and
sign. At this stage all Wick is in the primary horizontal ink, no need for
local potential covariance or picking a complement to curl relations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Corona
open Filter Set Function Finset Lattice MvPolynomial Symbols Source Source.Drops
open Next.Foundations Next.Rank Next.Rank.Normal PertExtension
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G: Gauge} {d : ℕ} {q : ℕ+} {S : Finset Cover} {R:Type*}

-- operations under relabelling

def flag (p:Face ℤ) : RG.Slot:=⟨route 0 p.1 1,p.2⟩
@[simp] lemma locates (p:Face ℤ): Tally (flag p)=p:=congr_arg (fun x=> (x,p.2)) (route_end ..)

def plow (s : Signed)(z:Cover)(p:Crumb G): Crumb G:= (flag (Face.send s z (Tally p.1)),p.2)
def scribe (s:Signed)(z:Cover) (p:Crumb G):Crumb G→₀ℂ := Finsupp.single (plow s z p) (↑(Next.Free.turned s p.1.plaq):ℂ)

def escort (s:Signed)(z:Cover):Primary G →ₐ[ℂ] Primary G:= exchange (scribe s z)

lemma fling (s:Signed)(z:Cover) (p : Primary G) (A:Links ℤ G.Color):
   demonstrates A (escort s z p)=demonstrates (tour s z A) p:=by
   unfold escort demonstrates; rw [reads_val]
   apply congr_arg (fun m=>aeval m p); funext i; rw [reads,scribe,Finsupp.linearCombination_single,smul_eq_mul]
   simp only [lanes,plow,locates,stroll, PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul]
lemma journeys (s:Signed)(z:Cover)(p:Primary G): escort s z (icing p)=icing (escort s z p):=by
 unfold escort icing; rw [prepared]
 rw [show scope (scribe s z) (ambient G)=ambient G from ?_]
 ext1; funext i j
 have he:=orbit_value (p:=i) (q:=j) (p':=plow s z i) (q':=plow s z j) s z (locates _|>.symm) (locates _|>.symm) rfl rfl
 change treats (ambient G) _ _=_
 unfold treats scribe; simp only [Finsupp.linearCombination_single,Pi.smul_apply,smul_eq_mul];rw [he, Complex.ofReal_mul]; ring
lemma recedes (s:Signed) (z:Cover) (p:Primary G) : escort s z (thawed p)=thawed (escort s z p):=by
 rw [← thawed_ice (escort s _ _), ← journeys, icing_thaw]

lemma pigmented (p:Primary G) (u:G.El) (A:Links ℤ G.Color):
    demonstrates A (Hue.inked u p)=demonstrates (badge u A) p:=by
  let m:= fun i: RG.Slot=> act (Tally i) A
  change Hue.display m (Hue.inked u p)=Hue.display (fun i=> act (Tally i) (badge u A)) p
  rw [← Hue.hue]; apply congr_arg (fun f=>Hue.display f p)
  funext i; unfold badge Hue.tint m; rw [act_simple,act_simple]; simp only [map_add,map_sub]; rfl
lemma hues (p: Primary G)(u:G.El): Hue.inked u (icing p)=icing (Hue.inked u p):= Hue.colored_milk ..
lemma hues_thaw (p: Primary G)(u:G.El): Hue.inked u (thawed p)=thawed (Hue.inked u p):=by rw [← thawed_ice (Hue.inked u _), ← hues, icing_thaw]

abbrev frost (p:Primary G): Primary G:= Next.Rank.Spindle.retro _ p
lemma star_ice (p:Primary G) : frost (icing p)=icing (frost p):=by
 apply Eq.symm; apply Next.Rank.Spindle.flashed; intro i j; unfold ambient LatticePT.covarianceSymbol; dsimp; split_ifs <;> simp
lemma star_thaw (p:Primary G) : frost (thawed p)=thawed (frost p):=by rw [← thawed_ice (frost _),← star_ice, icing_thaw]
lemma demonstrates_frost (p:Primary G)(A:Links ℤ G.Color):
   demonstrates A (frost p)=star (demonstrates A p):=Next.Rank.Spindle.escorted (fun i:Crumb G=>act (Tally i.1) A i.2) p

-- bridge

def Binds (p: Primary G)(v: LocalPol G S) := ∀ A, inscribe (Symbols.patch S A) v=demonstrates A p

lemma act_scale (u:Face ℤ) (A:Links ℤ G.Color) (r:ℝ) : act u (r • A)= r • act u A := by rw [act_simple,act_simple]; simp [smul_add,smul_sub]
lemma binds_degree {p:Primary G}{v:LocalPol G S}(h:Binds p v)(k:ℕ): Binds (portion k p) (portion k v):=by
 intro A; rw [portion_rays]; unfold demonstrates; rw [solidarity]; apply congr_arg (CubicMatch.term k); funext x
 rw [h]; have he j : lanes (x • A) j=x • lanes A j:=by simp only [lanes,act_scale, PiLp.smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_mul]
 exact congr_arg (fun g=>aeval g p) (funext he)

def scape (G : Gauge) (d:ℕ) : Primary G →ₗ[ℂ] Labels.Pol G:=
  (∑ k∈ Finset.range (d+1), weightedHomogeneousComponent Labels.generation k) ∘ₗ (Heat.Ray.print d).toLinearMap
lemma printed (p:Primary G)(d : ℕ): scape G d p=Heat.Ray.clipped d p:=by simp only [scape,LinearMap.comp_apply,LinearMap.sum_apply]; rfl
lemma scape_res {d':ℕ} (h:d≤d') (p:Primary G): capRead d (scape G d' p)=scape G d p:=by
 rw [printed,printed,← Heat.Ray.cap_depth p h]; unfold Heat.Ray.clipped; ext i; simp only [coeff_capRead]; split_ifs <;> first | rfl | omega
lemma scape_account {p v:Primary G}(h:Accounts p v): scape G d p=scape G d v:=by
 rw [printed,printed,Heat.Ray.clipped,Heat.Ray.clipped]; apply congr_arg
 apply Labels.eval_ext; intro J; rw [Heat.Ray.display_jet,Heat.Ray.display_jet]; exact h (access (trunk d J))
lemma stage_zero (H:Hol G) (p: Feed.LogSeries G S) (d:ℕ):
    Feed.stage H d 0 p = Feed.booth H d 0 (p 0):= by rw [Feed.stage_at]; simp
lemma bonded (H:Hol G) {p:Primary G} {P:LocalPol G S} (h:Binds p P) : Feed.booth H d 0 P=scape G d p:=by
 rw [printed]; rw (occs:=.pos [1]) [← Feed.slots_full (Heat.Ray.clipped d p) (cap_limited ..: Heat.Ray.clipped d p ∈ Labels.limited G d)]
 unfold Feed.booth; simp only [LinearMap.sum_apply,Nat.add_zero,LinearMap.comp_apply]
 apply Finset.sum_congr rfl; intro k hk
 rw [show portion k (Heat.Ray.clipped d p)=Heat.Ray.clipped d (portion k p) from ?_, Feed.portion_letter H d (portion k P) k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)), Heat.Ray.clipped]
 · apply congr_arg; apply Labels.eval_ext; intro J
   rw [Feed.letter_diagonal H d (portion_in P k),Heat.Ray.display_jet]
   exact binds_degree h k ..
 unfold Heat.Ray.clipped
 rw [← Feed.cap_portion]
 exact congr_arg _ (Heat.Ray.ink_cut p k|>.symm)

lemma real_scaped (p q:Primary G)(d:ℕ) (h:∀ A, demonstrates A p=star (demonstrates A q)):
    scape G d p=Labels.conjPol (scape G d q):=by
 rw [printed,printed,Heat.Ray.clipped,Heat.Ray.clipped, show Heat.Ray.print d p=Labels.conjPol (Heat.Ray.print d q) from ?_]
 · ext i; simp only [Labels.conjPol,coeff_map,coeff_capRead]; split_ifs <;> simp
 apply Labels.eval_ext; intro J; rw [Heat.Ray.display_jet, Labels.conj_value,Heat.Ray.display_jet]; exact h _
end YM.Comparison.Stencils.Corona
