import YM.Integration.WilsonNeutralPointWeakLedger
import YM.FormalBulk08.Clover.Eve

/-! The single-child normalized graph equation, with its original triangular
coefficients and one gain on the current weak component. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointWeakTransfer
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Quire Palm Grail Chapel Borough Sable Tundra Aster Clover Series Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels WilsonNeutralPointWeakLedger
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical

variable {G:Gauge}{K:KernelChoices}{d D E e r u:ℕ}{X:Type}{B:Frame G d}
variable {J Q:X→ℕ}{F:∀i:X,Flight (J i) (Q i)}{V:∀i:X,Lodge (F i).patch}
variable {Z:∀i,Train (J i)}{H:∀i,(F i).patch.Branches K G}{ρ:ChartRatio G}{a:hue G}
variable {τ:Time X}{σ η δ μ:X→ℝ}{o:Loc G 1}{W:X→Pot G}

private theorem rest {A:X→Plaza B D}{M:X→Tilework B}{b:X→Letter B→ℝ}
    (v:Letter B)(file:∀i,Colfax (slots B) (Pose.weight B) (M i) (b i))
    (curr:∀i,Court o B (A i))
    (cap:∀y j,j<e ∨ j=e∧r ≤ slots B y → Faint τ (fun _=>1) (fun i=>coeff j (M i y v)))
    (lo:∀y j k,itinerary B v e r y j k→Sigh u τ o (fun _=>1) (fun i p=>A i y p j k)):
    Sigh u τ o (fun _=>1) (fun i p=>Clover.track B (A i) (M i) v p e r):=by
  unfold Sigh Whey Clover.track
  apply bear_sums _
  rintro ⟨y,t,s⟩ hs
  obtain ⟨dif,mem⟩:=Finset.mem_erase.mp hs
  have total:t+s=e:=Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_product.mp mem).2
  by_cases vanish:slots B y+s<r
  · simp_rw [seat_void v y vanish _ _ (curr _)];exact bear_void ..
  have price:=cap y t (by omega)
  by_cases top:t=0
  · subst t
    have eq:s=e:=by omega
    have other:v≠y:=fun h=>dif (by rw [h,eq])
    subst s
    by_cases prev:itinerary B v e r y e r
    · exact fading (lo y e r prev) price
    have none i:coeff 0 (M i y v)=0:=Classical.byContradiction fun live=>
      prev (ord_only ((file i).peers y v live other.symm))
    simp only [Clover.tickets,none,zero_smul];exact bear_void ..
  exact fading (lo y s r (.inl (by omega))) price

private theorem remove {T S A Y:X→Studio D→Tile (edgeL G) r}{b:X→ℝ}
    (h:Sugar o τ u μ (fun _=>1) r T S)(p:Sigh u τ o (fun _=>1) Y)
    (eq:∀i f,S i f=b i • A i f+Y i f)(lo:∀i,1≤b i):
    Sugar o τ u μ (fun _=>1) r T A:=by
  obtain ⟨C,soft,nonneg,buy⟩:=h
  obtain ⟨B,cap,le,paid⟩:=p
  refine ⟨_,soft.plus cap,fun i=>add_nonneg (nonneg i) (le i),fun i M hM fine f=>?_⟩
  have got:=buy i M hM fine f
  rw [eq] at got
  apply (Clover.earns got (paid i f) (lo i)).mono
  apply le_of_eq;ring

variable {T A:X→Plaza B D}
variable (w:Wells τ F V H ρ a σ η δ Z Z W W E)
variable (credit:Soft τ (fun i=>(η i)⁻¹))(hL:∀i,2≤(F i).L.val)(digit:∀i,Site (F i).L)
variable (wallet:Ledger K B o (graded F Z) V digit E d D u τ μ)

abbrev block (hL:∀i,2≤(F i).L.val)(digit:∀i,Site (F i).L)(i:X)(Y:Plaza B D):Plaza B D:=
  WilsonNeutralPointMatrix.child (graded F Z i) (V i) (W i) a ρ (H i) (hL i) d d (digit i) ∘ Y

include w credit wallet in
theorem column (v:Letter B)(he:e≤E)(rank:r≤e+slots B v)
    (upper:∀i,Court o B (T i))(lower:∀i,Court o B (A i))
    (M:X→Tilework B)(income:∀i,M i=pantry B (block (Z:=Z) (V:=V) (W:=W) (H:=H) (ρ:=ρ) (a:=a) hL digit i (T i)))
    (born:∀i,Colfax (slots B) (Pose.weight B) (M i) (fun v=>heightK (F i).L d (Pose.weight B v)))
    (exactly:∀i,larch (A i) (M i)=block (Z:=Z) (V:=V) (W:=W) (H:=H) (ρ:=ρ) (a:=a) hL digit i (T i))
    (old:∀j m,precede e r j m→Wayfarer (fun i=>T i v) j m u τ o (fun _=>1))
    (smaller:∀y j k,itinerary B v e r y j k→Sigh u τ o (fun _=>1) (fun i p=>A i y p j k)):
    Sugar o τ u μ (fun _=>1) r (fun i p=>T i v p e r) (fun i p=>A i v p e r) ∧
      ∀j y,j<e ∨ j=e∧r ≤ slots B y→Faint τ (fun _=>1) (fun i=>coeff j (M i y v)):=by
  let out(i:X):=block (Z:=Z) (V:=V) (W:=W) (H:=H) (ρ:=ρ) (a:=a) hL digit i (T i) v
  have paid:Resolved d r e u (graded F Z) V K hL digit o τ (fun _=>1) (fun i=>T i v) out:=
    heard w credit (fun _=>zero_le_one) hL digit he old d d
  have size:r≤d+E:=by have:=slotsFits B v;omega
  have rates j y (focus:j<e∨j=e∧r ≤ slots B y):Faint τ (fun _=>1) (fun i=>coeff j (M i y v)):=by
    simp_rw [income]
    exact projected wallet paid old he size (fun i=>(upper i).officers v) (slotsFits B v)
      (fun y=>rent_city v y upper e) (fun _=>zero_le_one) j y focus
  have hz:=rest v born lower (fun y j focus=>rates j y focus) smaller
  have whole:=diagonal wallet paid old he size (fun i=>(upper i).officers v) (slotsFits B v)
    (fun y=>rent_city v y upper e) (fun _=>zero_le_one)
  refine ⟨remove (b:=fun i=>heightK (F i).L d (Pose.weight B v)) whole hz ?_ (fun i=>crown_weight _ _),rates⟩
  intro i p
  change (block (Z:=Z) (V:=V) (W:=W) (H:=H) (ρ:=ρ) (a:=a) hL digit i (T i)) v p e r=_
  rw [←exactly,employee,(born i).due]

end YM.Integration.WilsonNeutralPointWeakTransfer
end
