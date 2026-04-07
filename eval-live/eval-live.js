/**
 * Render evaluation tables into a container element.
 * @param {HTMLElement|string} container - DOM element or element ID
 * @param {Object} data - Dict of table name -> array of row objects
 */
function initEvalLive(container, data) {
  if (typeof container === "string") {
    container = document.getElementById(container);
  }
  container.classList.add("eval-live");
  container.innerHTML = "";

  for (const [tableName, rows] of Object.entries(data)) {
    if (!Array.isArray(rows) || rows.length === 0) continue;

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
    // Expand column header
    const thExpand = document.createElement("th");
    thExpand.className = "expand-col";
    headerRow.appendChild(thExpand);
    for (const col of cols) {
      const th = document.createElement("th");
      th.textContent = col;
      headerRow.appendChild(th);
    }
    thead.appendChild(headerRow);
    table.appendChild(thead);

    const tbody = document.createElement("tbody");
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
    }
    table.appendChild(tbody);

    const wrap = document.createElement("div");
    wrap.className = "table-wrap";
    wrap.appendChild(table);
    section.appendChild(wrap);
    container.appendChild(section);
  }
}
