//
// generated code goes here
//

int main(void) {

    // h_nodes 
    auto nodes_tuple = thrust::make_tuple<descend::i32, descend::i32>(0, 2);
    auto nodes = descend::create_array<64, descend::tuple<descend::i32, descend::i32>>(nodes_tuple);
    for (int i = 0; i < 64; i++) {
      if (2*i < 64) {
        thrust::get<0>(nodes[i]) = 2*i;  
      } else {
        thrust::get<0>(nodes[i]) = -1;
        thrust::get<1>(nodes[i]) = -1;
      }
    }
    const auto h_nodes = descend::HeapBuffer<descend::array< descend::tuple<descend::i32, descend::i32>, 64>>(nodes);


    // h_edges
    auto edges = descend::create_array<63, descend::i32>(0);
    for (int i = 0; i < 63; i++) {
      edges[i] = i+1;
    }
    const auto h_edges = descend::HeapBuffer<descend::array<descend::i32, 63>>(edges);

    // h_changes (mask, updating mask, visited, cost)
    auto changes_tuple = thrust::make_tuple<bool, bool, bool, descend::i32>(false, false, false, -1);
    auto changes = descend::create_array<64, descend::tuple<bool, bool, bool, descend::i32>>(changes_tuple);
    thrust::get<0>(changes[0]) = true; 
    thrust::get<2>(changes[0]) = true;
    thrust::get<3>(changes[0]) = 0;
    auto h_changes = descend::HeapBuffer<descend::array< descend::tuple<bool, bool, bool, descend::i32>, 64>>(changes);


    bool h_stop = true;
    

    bfs<64, 63>(&h_nodes, &h_edges, &h_changes, &h_stop);

    for (int i = 0; i < 64; i++) {
      std::cout << thrust::get<0>(h_changes[i]) 
        << thrust::get<1>(h_changes[i]) 
        << thrust::get<2>(h_changes[i]) 
        << thrust::get<3>(h_changes[i]) << std::endl;
    }

  exit(EXIT_SUCCESS);
}
