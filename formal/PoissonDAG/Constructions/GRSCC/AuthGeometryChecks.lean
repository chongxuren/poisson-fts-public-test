import PoissonDAG.Constructions.GRSCC.AuthGeometry

namespace PoissonDAG.GRSCC
namespace AuthenticationGeometry
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem all_lanes_connected : ∀ (s : Slot) (g : Lane) (e : Fin 9),
    laneConnected s g e = true := by intro s; fin_cases s <;> decide +kernel

theorem lane_exits_continue : ∀ (s : Slot) (d : Fin 5),
    exitVertex s d.castSucc = entryVertex s d.succ := by intro s; fin_cases s <;> decide +kernel

theorem terminal_exit : ∀ s : Slot, exitVertex s 5 = 846 := by intro s; fin_cases s <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 30000000 in
theorem all_lanes_separated : ∀ (s : Slot) (g h : Lane) (e : Fin 9),
    separated s g h e = true := by intro s; fin_cases s <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem work_bound : ∀ (s : Slot) (g : Lane) (e : Fin 9),
    (work s g e).all (fun w => decide (w < 847)) = true := by intro s; fin_cases s <;> decide +kernel

theorem opening_bound : ∀ (s : Slot) (g : Lane) (e : Fin 9),
    opening s g e < 846 := by intro s; fin_cases s <;> decide +kernel

end AuthenticationGeometry

end PoissonDAG.GRSCC
