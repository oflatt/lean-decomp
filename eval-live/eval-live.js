/**
 * Render evaluation tables into a container element.
 * @param {HTMLElement|string} container - DOM element or element ID
 * @param {Object} data - Dict of table name -> array of row objects
 * @param {string} [name] - Project name shown in the heading
 * @param {string} [graphScript] - Python script using eval_live decorators
 * @param {string} [evalLivePy] - Source of the eval_live.py library
 */
function initEvalLive(container, data, name, graphScript, evalLivePy) {
  if (typeof container === "string") {
    container = document.getElementById(container);
  }
  container.classList.add("eval-live");
  container.innerHTML = "";

  if (name) {
    const h1 = document.createElement("h1");
    h1.className = "eval-live-title";
    h1.textContent = name + " \u2014 Eval Live";
    container.appendChild(h1);
  }

  // Graph engine — initialized async
  let graphEngine = null;

  // Graphs section
  if (graphScript && evalLivePy) {
    const graphSection = document.createElement("div");
    graphSection.className = "graph-section";
    const graphStatus = document.createElement("div");
    graphStatus.className = "graph-status";
    graphStatus.textContent = "Loading Pyodide...";
    graphSection.appendChild(graphStatus);
    container.appendChild(graphSection);

    initGraphEngine(graphSection, graphStatus, data, graphScript, evalLivePy, container).then((engine) => {
      graphEngine = engine;
    });
  }

  // Track per-table filter state
  const tableStates = [];
  // Computed tables added later by the engine
  const computedTableStates = [];
  // Placeholder for computed tables
  const computedTablesContainer = document.createElement("div");

  // Called when a RAW table's text filter changes
  function onRawFilterChange() {
    const filteredData = {};
    for (const ts of tableStates) {
      filteredData[ts.tableName] = ts.visibleRows;
    }
    if (graphEngine) {
      graphEngine.rerender(filteredData);
    }
  }

  // Called when a COMPUTED table's text filter changes
  function onComputedFilterChange() {
    if (graphEngine) {
      graphEngine.applyComputedFilters();
    }
  }

  // Expose state for the graph engine
  container._evalLiveOnRawFilterChange = onRawFilterChange;
  container._evalLiveOnComputedFilterChange = onComputedFilterChange;
  container._evalLiveTableStates = tableStates;
  container._evalLiveComputedTableStates = computedTableStates;
  container._evalLiveComputedContainer = computedTablesContainer;
  container._evalLiveOriginalData = data;

  for (const [tableName, rows] of Object.entries(data)) {
    if (!Array.isArray(rows) || rows.length === 0) continue;
    const section = buildTable(tableName, rows, tableStates, onRawFilterChange);
    container.appendChild(section);
  }

  container.appendChild(computedTablesContainer);
}

/**
 * Build a table section DOM element.
 * @param {string} tableName
 * @param {Array} rows
 * @param {Array} tableStates - array to push state into
 * @param {Function} onFilterChange - called when filters change
 * @returns {HTMLElement}
 */
function buildTable(tableName, rows, tableStates, onFilterChange) {
  const tableState = { tableName, rows, visibleRows: rows };
  tableStates.push(tableState);

  const section = document.createElement("div");
  section.className = "table-section";

  const heading = document.createElement("h2");
  heading.textContent = tableName;
  const rowCount = document.createElement("span");
  rowCount.className = "row-count";
  rowCount.textContent = `(${rows.length} rows)`;
  heading.appendChild(rowCount);
  section.appendChild(heading);

  const cols = [...new Set(rows.flatMap(Object.keys))];

  const table = document.createElement("table");

  const thead = document.createElement("thead");
  const headerRow = document.createElement("tr");
  const thExpand = document.createElement("th");
  thExpand.className = "expand-col";
  headerRow.appendChild(thExpand);
  for (const col of cols) {
    const th = document.createElement("th");
    th.textContent = col;
    headerRow.appendChild(th);
  }
  thead.appendChild(headerRow);

  // Filter row
  const filterRow = document.createElement("tr");
  filterRow.className = "filter-row";
  const filterExpandTh = document.createElement("th");
  filterExpandTh.className = "expand-col";
  filterRow.appendChild(filterExpandTh);
  const filters = [];
  for (const col of cols) {
    const th = document.createElement("th");
    const input = document.createElement("input");
    input.type = "text";
    input.className = "filter-input";
    input.placeholder = "filter...";
    filters.push({ col, input });
    th.appendChild(input);
    filterRow.appendChild(th);
  }
  thead.appendChild(filterRow);
  table.appendChild(thead);

  const tbody = document.createElement("tbody");
  const rowEls = [];
  for (const row of rows) {
    const tr = document.createElement("tr");
    tr.classList.add("collapsed");

    const tdBtn = document.createElement("td");
    tdBtn.className = "expand-col";
    const btn = document.createElement("button");
    btn.className = "expand-btn";
    btn.textContent = "+";
    btn.addEventListener("click", () => {
      const collapsed = tr.classList.toggle("collapsed");
      btn.textContent = collapsed ? "+" : "\u2212";
    });
    tdBtn.appendChild(btn);
    tr.appendChild(tdBtn);

    for (const col of cols) {
      const td = document.createElement("td");
      const val = row[col];
      td.textContent = val === undefined ? "" : typeof val === "object" ? JSON.stringify(val) : String(val);
      tr.appendChild(td);
    }
    tbody.appendChild(tr);
    rowEls.push({ tr, row });
  }

  function applyFilters() {
    let visible = 0;
    const filtered = [];
    for (const { tr, row } of rowEls) {
      let show = true;
      for (const { col, input } of filters) {
        const query = input.value.toLowerCase();
        if (!query) continue;
        const val = row[col];
        const text = val === undefined ? "" : typeof val === "object" ? JSON.stringify(val) : String(val);
        if (!text.toLowerCase().includes(query)) {
          show = false;
          break;
        }
      }
      tr.style.display = show ? "" : "none";
      if (show) { visible++; filtered.push(row); }
    }
    rowCount.textContent = `(${visible}/${rows.length} rows)`;
    tableState.visibleRows = filtered;
    onFilterChange();
  }
  for (const { input } of filters) {
    input.addEventListener("input", applyFilters);
  }

  table.appendChild(tbody);
  const wrap = document.createElement("div");
  wrap.className = "table-wrap";
  wrap.appendChild(table);
  section.appendChild(wrap);

  tableState.applyFilters = applyFilters;
  tableState.rowEls = rowEls;
  tableState.rowCount = rowCount;

  return section;
}

/**
 * Show/hide rows in a raw table based on filtered data from apply_table_filters.
 * @param {Object} filteredData - {tableName: [rows]}
 * @param {Array} rawTableStates
 */
function applyFilteredDataToRawTables(filteredData, rawTableStates) {
  for (const ts of rawTableStates) {
    const allowed = filteredData[ts.tableName];
    if (!allowed) continue;
    const allowedSet = new Set(allowed.map(r => JSON.stringify(r)));
    const filtered = [];
    for (const { tr, row } of ts.rowEls) {
      const show = allowedSet.has(JSON.stringify(row));
      tr.style.display = show ? "" : "none";
      if (show) filtered.push(row);
    }
    ts.visibleRows = filtered;
    ts.rowCount.textContent = `(${filtered.length}/${ts.rows.length} rows)`;
  }
}

async function initGraphEngine(section, status, data, graphScript, evalLivePy, container) {
  try {
    const pyodide = await loadPyodide();
    status.textContent = "Installing matplotlib...";
    await pyodide.loadPackage("matplotlib");
    status.textContent = "Running graph script...";

    pyodide.FS.writeFile("/home/pyodide/eval_live.py", evalLivePy);
    await pyodide.runPythonAsync(graphScript);

    // Graph UI
    const bar = document.createElement("div");
    bar.className = "graph-bar";
    section.appendChild(bar);
    const display = document.createElement("div");
    display.className = "graph-display";
    section.appendChild(display);

    let activeGraphName = null;

    async function renderGraphs(inputData) {
      pyodide.globals.set("__eval_live_data__", pyodide.toPy(inputData));
      const resultProxy = await pyodide.runPythonAsync(
        "import eval_live; eval_live.registry.run_graphs(__eval_live_data__)"
      );
      const graphs = resultProxy.toJs({ create_proxies: false });
      resultProxy.destroy();
      return graphs;
    }

    async function renderTables(inputData) {
      pyodide.globals.set("__eval_live_data__", pyodide.toPy(inputData));
      const resultProxy = await pyodide.runPythonAsync(
        "import eval_live; eval_live.registry.run_tables(__eval_live_data__)"
      );
      const tables = resultProxy.toJs({ create_proxies: false });
      resultProxy.destroy();
      return tables.map(t => ({
        name: t.get("name"),
        rows: t.get("rows").map(r => Object.fromEntries(r.entries())),
        hasFilterSource: t.get("has_filter_source"),
      }));
    }

    async function callApplyTableFilters(tableFilters, inputData) {
      pyodide.globals.set("__eval_live_data__", pyodide.toPy(inputData));
      pyodide.globals.set("__eval_live_table_filters__", pyodide.toPy(tableFilters));
      const resultProxy = await pyodide.runPythonAsync(
        "import eval_live; eval_live.registry.apply_table_filters(__eval_live_table_filters__, __eval_live_data__)"
      );
      const result = resultProxy.toJs({ create_proxies: false });
      resultProxy.destroy();
      // Convert to plain JS object
      const out = {};
      for (const [k, v] of result.entries()) {
        if (Array.isArray(v)) {
          out[k] = v.map(r => r instanceof Map ? Object.fromEntries(r.entries()) : r);
        } else {
          out[k] = v;
        }
      }
      return out;
    }

    async function showGraphs(inputData) {
      const graphs = await renderGraphs(inputData);
      if (!graphs || graphs.length === 0) {
        status.textContent = "No graphs registered.";
        return;
      }

      const graphMap = new Map();
      for (const g of graphs) {
        graphMap.set(g.get("name"), g.get("src"));
      }

      if (bar.children.length === 0) {
        for (const g of graphs) {
          const gName = g.get("name");
          const btn = document.createElement("button");
          btn.className = "graph-btn";
          btn.textContent = gName;
          btn.addEventListener("click", () => {
            for (const b of bar.querySelectorAll(".graph-btn")) b.classList.remove("active");
            btn.classList.add("active");
            activeGraphName = gName;
            display.innerHTML = "";
            const src = graphMap.get(gName);
            if (src) {
              const img = document.createElement("img");
              img.src = src;
              img.alt = gName;
              display.appendChild(img);
            }
          });
          bar.appendChild(btn);
        }
        activeGraphName = graphs[0].get("name");
        bar.querySelector(".graph-btn").click();
      } else {
        if (activeGraphName && graphMap.has(activeGraphName)) {
          display.innerHTML = "";
          const img = document.createElement("img");
          img.src = graphMap.get(activeGraphName);
          img.alt = activeGraphName;
          display.appendChild(img);
        }
      }
    }

    // Track which computed tables have filter_source
    let computedTableMeta = [];

    async function showComputedTables(inputData) {
      const tables = await renderTables(inputData);
      const ctContainer = container._evalLiveComputedContainer;
      const ctStates = container._evalLiveComputedTableStates;
      const onComputedFilterChange = container._evalLiveOnComputedFilterChange;

      ctContainer.innerHTML = "";
      ctStates.length = 0;
      computedTableMeta = tables.map(t => ({
        name: t.name,
        hasFilterSource: t.hasFilterSource,
      }));

      for (const { name, rows } of tables) {
        if (!rows || rows.length === 0) continue;
        const sect = buildTable(name, rows, ctStates, onComputedFilterChange);
        ctContainer.appendChild(sect);
      }
    }

    /**
     * Called when a computed table's text filter changes.
     * Collects visible rows from all computed tables that have filter_source,
     * calls apply_table_filters in Python to get filtered raw data,
     * then applies that to the raw table DOM.
     */
    async function applyComputedFilters() {
      const ctStates = container._evalLiveComputedTableStates;
      const rawTableStates = container._evalLiveTableStates;
      const originalData = container._evalLiveOriginalData;

      // Build table_filters list for Python
      const tableFilters = [];
      for (const ct of ctStates) {
        const meta = computedTableMeta.find(m => m.name === ct.tableName);
        if (meta && meta.hasFilterSource) {
          tableFilters.push({ name: ct.tableName, filtered_rows: ct.visibleRows });
        }
      }

      if (tableFilters.length === 0) return;

      const filteredData = await callApplyTableFilters(tableFilters, originalData);
      applyFilteredDataToRawTables(filteredData, rawTableStates);
    }

    // Initial render
    status.textContent = "";
    await showGraphs(data);
    await showComputedTables(data);

    // Debounced re-render for raw filter changes
    let rerenderTimer = null;
    function rerender(filteredData) {
      clearTimeout(rerenderTimer);
      rerenderTimer = setTimeout(async () => {
        // Re-run script to rebuild the registry
        pyodide.runPython("import eval_live; eval_live.registry = None");
        await pyodide.runPythonAsync(graphScript);
        await showGraphs(filteredData);
        await showComputedTables(filteredData);
      }, 300);
    }

    return { rerender, applyComputedFilters };
  } catch (err) {
    status.textContent = "Graph error: " + err.message;
    console.error(err);
    return null;
  }
}
