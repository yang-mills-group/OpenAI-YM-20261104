import YM.Integration.WilsonCenteredNestedTreeLeaves
import YM.Integration.WilsonCenteredNestedTreeMean

/-! Sharp two-vertex spatial truncation on the elected Wilson OPE reader.
Both actual centers and every filed child grade enter the same physical chord. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeSharp
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Log OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree OPE.Nesting.Composite
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedPairChord WilsonCenteredNestedTreeMean
open WilsonCenteredNestedRawRows WilsonCenteredNestedRawPair WilsonCenteredNestedPairHaar
open WilsonCenteredNestedChildEdit WilsonCenteredNestedTreeLeaves WilsonCenteredNestedPairConvoy
open WilsonCenteredNestedEdge WilsonCenteredNestedGross WilsonCenteredNestedLoggedRow
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

abbrev charge (v:full.Leaf→S.Tag) (m:ℕ) (a r:ℝ) := WilsonCenteredNestedTreeWallet.toll (degrees (roster v)) m a r

lemma rebate (v:full.Leaf→S.Tag) (m:ℕ) {a r:ℝ} (ap:0<a) (rp:0<r) :
    charge v m a r * base a r m (degree (near v)) (other v).1=1 := by
  unfold charge WilsonCenteredNestedTreeWallet.toll base degree
  rw [Fin.sum_univ_two]
  change (a^((near v 0).1+(near v 1).1)*r^(other v).1/r^m)*
    (r^m/(a^((near v 0).1+(near v 1).1)*r^(other v).1))=1
  field_simp

private lemma combine {u E1 E2:ℝ} {A B C:ℂ} (p:0≤u) (h1:u*‖A-B‖≤E1) (h2:u*‖B-C‖≤E2) :
    u*‖A-C‖≤E1+E2 := by
  have jump : ‖A-C‖ ≤ ‖A-B‖ + ‖B-C‖ := by
    rw [show A-C=(A-B)+(B-C) by abel]
    exact norm_add_le ..
  apply (mul_le_mul_of_nonneg_left jump p).trans
  rw [mul_add]
  exact add_le_add h1 h2

theorem tariffs (fac : Facilities C f S) (foundation:Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (v:full.Leaf→S.Tag) (D m:ℕ) (c:Q.channels m)
    {M η:ℝ} (Mn:0≤M) (ηp:0<η) : ∃(j k l:ℕ)(A B E:ℝ),0≤A ∧ 0≤B ∧ 0≤E ∧
      ∀ᶠr:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),Accept r M η (dates r a) z→
      charge v m a r * ‖Kernel.output F Q z v c - Kernel.chord F Q z v c (caps m D)‖ ≤
      (A*(shell r * shell a)^j + Fintype.card (Menu.Cut Q D)*wage k B a*wage l E r)*(a/r)^(D+1) := by
  obtain ⟨j,A,An,raw⟩ := WilsonCenteredNestedTreeMean.original F Q fac lo ticket (roster v) D m c Mn ηp
  obtain ⟨k,l,B,E,Bn,En,formed⟩ := WilsonCenteredNestedPairHaar.original F Q fac foundation lo ticket D m c (near v) (other v) Mn ηp
  refine ⟨j,k,l,A,B,E,An,Bn,En,?_⟩
  filter_upwards [raw,formed] with r atR atS a z ok
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have rp : 0<r := ok.levels.1
  have ar : a≤r := by
    have e : a≤r*1 := (ok.levels.2.2 (0:Fin 2)).2.1
    rwa [mul_one] at e
  have positive : 0≤charge v m a r := by unfold charge WilsonCenteredNestedTreeWallet.toll;positivity
  have first:=atR a z ok
  rw [WilsonCenteredNestedTreeLeaves.original,child_sites,root_sites,WilsonCenteredNestedTreeLeaves.inner] at first
  have second := atS a ap ar (skyline (childPlace 0 z)) (skyline z) (anchor z) (node_room (ok.relative.2.2 (0:Fin 2))) (node_room ok.relative)
  rw [chord] at second
  have bill := mul_le_mul_of_nonneg_left second positive
  have credit := rebate v m ap rp
  have cost : charge v m a r * (Fintype.card (Menu.Cut Q D) *
      (wage k B a * wage l E r * base a r m (degree (near v)) (other v).1 * (a/r)^(D+1))) =
      Fintype.card (Menu.Cut Q D)*wage k B a*wage l E r*(a/r)^(D+1) := by
    calc
      _ = (charge v m a r * base a r m (degree (near v)) (other v).1) *
          (Fintype.card (Menu.Cut Q D)*wage k B a*wage l E r*(a/r)^(D+1)) := by ring
      _ = _ := by rw [credit,one_mul]
  rw [cost] at bill
  exact (combine positive first bill).trans_eq (by ring)

private lemma harmonize {x y A B E n:ℝ} (x1:1≤x) (y1:1≤y) (An:0≤A) (Bn:0≤B) (En:0≤E)
    (nn:0≤n) (j k l:ℕ) :
    A*(x*y)^j + n*(B*y^k)*(E*x^l) ≤ (A+n*B*E)*(x*y)^(j+k+l) := by
  have one:=one_le_mul_of_one_le_of_one_le x1 y1
  have xn:=zero_le_one.trans x1
  have yn:=zero_le_one.trans y1
  have xle:=le_mul_of_one_le_right xn y1
  have yle:=le_mul_of_one_le_left yn x1
  have product : y^k*x^l≤(x*y)^(k+l) := by
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ yn yle k) (pow_le_pow_left₀ xn xle l) (pow_nonneg xn _) (pow_nonneg (mul_nonneg xn yn) _)
  have a := pow_le_pow_right₀ one (show j≤j+k+l by omega)
  have b := product.trans (pow_le_pow_right₀ one (show k+l≤j+k+l by omega))
  calc
    _ = A*(x*y)^j+(n*B*E)*(y^k*x^l) := by ring
    _ ≤ A*(x*y)^(j+k+l)+(n*B*E)*(x*y)^(j+k+l) := add_le_add
      (mul_le_mul_of_nonneg_left a An) (mul_le_mul_of_nonneg_left b (mul_nonneg (mul_nonneg nn Bn) En))
    _ = _ := by ring

theorem original (fac : Facilities C f S) (foundation:Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (v:full.Leaf→S.Tag) (D m:ℕ) (c:Q.channels m)
    {M η:ℝ} (Mn:0≤M) (ηp:0<η) : ∃(J:ℕ)(K:ℝ),0≤K ∧ ∀ᶠr:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),
      Accept r M η (dates r a) z→charge v m a r * ‖Kernel.output F Q z v c - Kernel.chord F Q z v c (caps m D)‖ ≤
      K * ((shell r * shell a)^J * (a/r)^(D+1)) := by
  obtain ⟨j,k,l,A,B,E,An,Bn,En,fits⟩ := tariffs F Q fac foundation lo ticket v D m c Mn ηp
  let n:ℝ:=Fintype.card (Menu.Cut Q D)
  have nn:0≤n:=Nat.cast_nonneg _
  refine ⟨j+k+l,A+n*B*E,add_nonneg An (mul_nonneg (mul_nonneg nn Bn) En),?_⟩
  filter_upwards [fits] with r paid a z ok
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have rp : 0<r := ok.levels.1
  have logs := harmonize (shell_one r) (shell_one a) An Bn En nn j k l
  exact (paid a z ok).trans ((mul_le_mul_of_nonneg_right logs (pow_nonneg (div_nonneg ap.le rp.le) (D+1))).trans_eq (by ring))

end YM.Integration.WilsonCenteredNestedTreeSharp
