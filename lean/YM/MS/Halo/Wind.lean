import YM.MS.Halo.Wisp
/-!
# Pace for classical YC. Rank independent of D and seed loops. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Halo
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Alps
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge} {n k h:ℕ}{b:Bool}{s t r q p:ℤ}{z:ℂ}{X F H: Rack G n}{U Y:Mield G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product S
abbrev Bay (U:Mield G n)(h:ℕ)(t r:ℤ): Prop:= ∀ i:G.ColorIndex,Pace (U i) h t r
namespace Bay
lemma plus (hF:Bay U h t r)(hp:Bay Y h t r): Bay (U+Y) h t r:= fun i=> (hF i).plus (hp i)
lemma minus (hF:Bay U h t r)(hp:Bay Y h t r): Bay (U-Y) h t r:= fun i=> (hF i).minus (hp i)
lemma cash (hF:Bay U h t r)(hp:star z=z): Bay (z • U) h t r:= fun i=> (hF i).cash hp
lemma axis (a:Arts.L n) (hF:Bay U h t r): Bay (axisP a U) (h+1) t r:= fun i=> (hF i).seek a
lemma taller (hF:Bay U h t r)(hp:r≤q): Bay U h t q:= fun i=> (hF i).taller hp
lemma Cartan (hF:Bay U h t r)(hp:Bay Y k p q): Bay (jaw G n U Y) (h+k) (t+p) (r+q):= by intro i; rw [chew]; exact Pace.total _ (fun j _=> Pace.total _ (fun k _=> ((hF j).times (hp k)).cash (by simp [rune])))
lemma traceC (hF:Bay U h t r)(ht: Bay Y k p q): Pace (sume U Y) (h+k) (t+p) (r+q):= Pace.total _ (fun i _=> (hF i).times (ht i))
lemma cov (a:Arts.L n): Bay (Motif.A n G a) 1 0 1:= fun _=> Pace.here _
lemma gh : Bay (cwave n G) 1 1 1:= fun _=>Pace.here _
lemma curls (a b:Arts.L n): Bay (F₀ a b:Mield G n) 2 0 1:= (Bay.axis a (cov b)).minus (Bay.axis b (cov a))
lemma CurlB (a b: Arts.L n)(he:star z=z): Bay (cur z a b:Mield G n) 2 0 2:= (Bay.taller (curls a b) (by norm_num)).plus ((Bay.Cartan (cov a) (cov b)).cash he)
end Bay
lemma blazeT (z:Chan G n): Pace (phase z • ( Motif.leaf (onX true z) ⋄ blazeV G n z )) 4 0 3:= by
  apply Pace.cash; swap; · unfold phase; split <;> simp
  rcases z with ⟨_|a,i⟩; exact (Pace.here _).times (((Bay.gh.Cartan Bay.gh).cash (z:=-1/2) (by simp)) i); exact (Pace.here _).times (Bay.Cartan (Bay.cov a) Bay.gh i)
lemma B₁_P (G:Gauge)(n:ℕ): Pace ( B₁ G n ) 4 0 3:= by
   refine Pace.plus (?v : Pace (top3 G n) 4 0 3) ( Pace.total _ (fun i _=> blazeT i)); refine Pace.cash (Pace.total _ (fun i _=> Pace.total _ (fun j _=> ?w))) (by simp); exact Pace.plus ( Bay.traceC (Bay.curls i j) (( Bay.cov i ).Cartan ( Bay.cov j ))) (Bay.traceC (( Bay.cov i ).Cartan ( Bay.cov j )) (Bay.curls i j))
lemma B₂_P (G:Gauge)(n:ℕ): Pace (B₂ G n) 4 0 4:= by
   let U(i j:Arts.L n):Bay (quill i j:Mield G n) 2 0 2:= (Bay.cov i).Cartan (Bay.cov j);
   unfold B₂ top4; refine Pace.cash (Pace.total _ (fun i _=> Pace.total _ (fun j _=> Bay.traceC (U i j) (U i j)))) (by simp)
end YM.MS.Halo
