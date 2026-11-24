import YM.Integration.WilsonOriginalTwoFlatIRHousing

/-! Exact centered parents of the actual submitted grid coordinates. All
labels and every proper face may use the one same torus origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHeterogeneousStopSites
open Lattice RG Wilson RG16.Literal Extraction Finset
open scoped Classical BigOperators Topology

theorem parent (S : Schedule) {N p c : ℕ} (hi : c≤N) (z : Cover)
    (inside : ∀ a, 2*|S.a N*(z a : ℝ)| < S.a c) :
    (S.toDepth hi p).parent (wrap (S.side N p) z)=0 := by
  let g:=S.toDepth hi p
  have fine:=S.a_pos N
  have scaled:=S.embeds_scale g
  have component (a) : 2*(z a).natAbs < g.count.val := by
    have magnitude : S.a N*((z a).natAbs : ℝ)=|S.a N*(z a : ℝ)| := by
      rw [abs_mul,abs_of_pos fine]
      congr 1
      rw [←show (((↑(z a).natAbs : ℤ) : ℝ))=_ from Int.cast_natCast _,Int.natCast_natAbs,Int.cast_abs]
    have paid : S.a N*(2*((z a).natAbs:ℝ))<S.a N*(g.count.val:ℝ) := by
      rw [scaled]
      linarith only [magnitude,inside a]
    exact_mod_cast (mul_lt_mul_iff_right₀ fine).mp paid
  apply Next.Rank.Station.owner g
  rw [show g.embed (0:Site (S.side c p))=0 from g.root.map_zero,separation,sub_zero]
  have bound : (univ.sup (fun a=>((lift (wrap (S.side N p) z)) a).natAbs)) ≤ (g.count.val-1)/2 := by
    apply Finset.sup_le
    intro a _
    apply (Corona.lap z a).trans
    have := component a
    omega
  have pos : 1≤g.count.val := g.count.property
  change 2*univ.sup (fun a=>((lift (wrap (S.side N p) z)) a).natAbs)<g.count.val
  omega

theorem embedded (S : Schedule) {f N p c : ℕ} (fine : f≤N) (live : c≤N) (o : Cover)
    (inside : 2*‖S.gridPoint f o‖ < S.a c) :
    (S.toDepth live p).parent ((S.toDepth fine p).embed (wrap (S.side f p) o))=0 := by
  let g:=S.toDepth fine p
  change (S.toDepth live p).parent (g.embed (wrap (S.side f p) o))=0
  rw [g.embed_wrap]
  apply parent
  intro a
  have scale : S.a N*(g.count.val:ℝ)=S.a f := S.embeds_scale g
  change 2*|S.a N*((g.count.val • o a : ℤ) : ℝ)| < _
  rw [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,←mul_assoc,scale]
  have coord : |S.a f*(o a:ℝ)|≤‖S.gridPoint f o‖ :=
    (show ‖(S.gridPoint f o) a‖≤_ from PiLp.norm_apply_le ..)
  linarith only [inside,coord]

theorem funded {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)
    {I : Type} {f N p c : ℕ} (fine : f≤N) (live : c≤N) (o : I → Lattice.Cover) (anchor : I)
    {M t : ℝ} (size : ∀ i, ‖R.family.S.gridPoint f (o i)‖ ≤ M*t)
    (room : 4*(M*t)<R.family.S.a c) :
    let site := fun i => (R.family.S.toDepth fine p).embed (snap R.family f p o i)
    ∀ i, (R.family.S.toDepth live p).parent (site i-site anchor)=0 := by
  intro site i
  have raw : site i-site anchor =
      (R.family.S.toDepth fine p).embed (wrap _ (o i-o anchor)) := by
    unfold site snap
    rw [Ratio.embed_wrap,Ratio.embed_wrap,Ratio.embed_wrap,smul_sub,map_sub]
  rw [raw]
  apply embedded
  rw [Frontier6.Road.grid_sub R.family f]
  have bound := (norm_sub_le (R.family.S.gridPoint f (o i)) (R.family.S.gridPoint f (o anchor))).trans
    (add_le_add (size i) (size anchor))
  linarith only [room,bound]

end YM.Integration.WilsonOriginalHeterogeneousStopSites

